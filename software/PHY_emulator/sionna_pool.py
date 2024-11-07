


import os
gpu_num = "" # Use "" to use the CPU

os.environ["CUDA_VISIBLE_DEVICES"] = f"{gpu_num}"


# Import Sionna
try:
    import sionna
# except ImportError as e:
except:
    # Install Sionna if package is not already installed
    # import os
    # os.system("pip install sionna")
    import sionna
    


import tensorflow as tf

# Avoid warnings from TensorFlow
tf.get_logger().setLevel('ERROR')



import matplotlib.pyplot as plt
import numpy as np
import time
import pickle

from sionna.mimo import StreamManagement

from sionna.ofdm import ResourceGrid, ResourceGridMapper, LSChannelEstimator, LMMSEEqualizer
from sionna.ofdm import OFDMModulator, OFDMDemodulator, ZFPrecoder, RemoveNulledSubcarriers

from sionna.channel.tr38901 import Antenna, AntennaArray, CDL, UMi, UMa, RMa
from sionna.channel import gen_single_sector_topology as gen_topology
from sionna.channel import subcarrier_frequencies, cir_to_ofdm_channel, cir_to_time_channel
from sionna.channel import ApplyOFDMChannel, ApplyTimeChannel, OFDMChannel

from sionna.fec.ldpc.encoding import LDPC5GEncoder
from sionna.fec.ldpc.decoding import LDPC5GDecoder

from sionna.mapping import Mapper, Demapper

from sionna.utils import BinarySource, ebnodb2no, sim_ber, QAMSource, flatten_last_dims, count_errors
from sionna.utils.metrics import compute_ber

from sionna.channel import FlatFadingChannel, AWGN

import equalization as eqz

import numpy as np






class OFDMMIMO(tf.keras.Model):
    """Simulate OFDM MIMO transmissions over a 3GPP 38.901 model.
    """
    def __init__(self, scenario='umi', perfect_csi=False, carrier_frequency=3.5e9,fft_size=128,
    num_ofdm_symbols=14,subcarrier_spacing=30e3,cyclic_prefix_length=20,num_ut=4,num_ut_ant=1,
    num_bs_ant=8, num_bits_per_symbol=4,coderate=1, dtype_bits=32):





        if dtype_bits==32:
            self.m_dtype = tf.complex64
            self.m_dtype_real = tf.float32
        elif dtype_bits==64:
            self.m_dtype = tf.complex128
            self.m_dtype_real = tf.float64
        else:
            raise ValueError("[OFDMMIMO] Unsupported number of bits.")
        super().__init__(dtype = self.m_dtype)

       

        self._scenario = scenario
        self._perfect_csi = perfect_csi

        # Internally set parameters
        self._carrier_frequency = carrier_frequency
        self._fft_size = fft_size
        self._subcarrier_spacing = subcarrier_spacing 
        self._num_ofdm_symbols = num_ofdm_symbols
        self._cyclic_prefix_length = cyclic_prefix_length
        self._pilot_ofdm_symbol_indices = [2, 11]
        self._num_bs_ant = num_bs_ant
        self._num_ut = num_ut
        self._num_ut_ant = num_ut_ant
        self._num_bits_per_symbol = num_bits_per_symbol
        self._coderate = coderate





        # Create an RX-TX association matrix
        # rx_tx_association[i,j]=1 means that receiver i gets at least one stream
        # from transmitter j. Depending on the transmission direction (uplink or downlink),
        # the role of UT and BS can change.
        bs_ut_association = np.zeros([1, self._num_ut])
        bs_ut_association[0, :] = 1
        self._rx_tx_association = bs_ut_association
        self._num_tx = self._num_ut
        self._num_streams_per_tx = self._num_ut_ant


        # Setup an OFDM Resource Grid
        self._rg = ResourceGrid(num_ofdm_symbols=self._num_ofdm_symbols,
                                fft_size=self._fft_size,
                                subcarrier_spacing=self._subcarrier_spacing,
                                num_tx=self._num_tx,
                                num_streams_per_tx=self._num_streams_per_tx,
                                cyclic_prefix_length=self._cyclic_prefix_length,
                                pilot_pattern="kronecker",
                                pilot_ofdm_symbol_indices=self._pilot_ofdm_symbol_indices,
                                dtype=self.m_dtype)


        
        # Precompute indices to extract data symbols
        mask = self._rg.pilot_pattern.mask
        num_data_symbols = self._rg.pilot_pattern.num_data_symbols
        data_ind = tf.argsort(flatten_last_dims(mask), direction="ASCENDING")
        self._data_ind = data_ind[...,:num_data_symbols]


        # Setup StreamManagement
        self._sm = StreamManagement(self._rx_tx_association, self._num_streams_per_tx)

        # Configure antenna arrays
        self._ut_array = AntennaArray(
                                 num_rows=1,
                                 num_cols=1,
                                 polarization="single",
                                 polarization_type="V",
                                 antenna_pattern="omni",
                                 carrier_frequency=self._carrier_frequency,
                                 dtype=self.m_dtype)

        self._bs_array = AntennaArray(num_rows=1,
                                      num_cols=int(self._num_bs_ant/2),
                                      polarization="dual",
                                      polarization_type="cross",
                                      antenna_pattern="38.901",
                                      carrier_frequency=self._carrier_frequency,
                                      dtype=self.m_dtype)

        # Configure the channel model
        self._simple_mimo = False
        if self._scenario == 'awgn':
            self._channel_model = AWGN(dtype=self.m_dtype)
            self._simple_mimo = True
        elif self._scenario == 'flatfading': # transmissions over an i.i.d. Rayleigh fading channel.
            spatial_corr = None
            self._channel_model = FlatFadingChannel(self._num_ut,
                                         self._num_bs_ant,
                                         spatial_corr=spatial_corr,
                                         add_awgn=True,
                                         return_channel=True,
                                         dtype=self.m_dtype)
            self._simple_mimo = True
        elif self._scenario == "umi":
            self._channel_model = UMi(carrier_frequency=self._carrier_frequency,
                                      o2i_model="low",
                                      ut_array=self._ut_array,
                                      bs_array=self._bs_array,
                                      direction="uplink",
                                      enable_pathloss=False,
                                      enable_shadow_fading=False,
                                      dtype=self.m_dtype)
        elif self._scenario == "uma":
            self._channel_model = UMa(carrier_frequency=self._carrier_frequency,
                                      o2i_model="low",
                                      ut_array=self._ut_array,
                                      bs_array=self._bs_array,
                                      direction="uplink",
                                      enable_pathloss=False,
                                      enable_shadow_fading=False,
                                      dtype=self.m_dtype)
        elif self._scenario == "rma":
            self._channel_model = RMa(carrier_frequency=self._carrier_frequency,
                                      ut_array=self._ut_array,
                                      bs_array=self._bs_array,
                                      direction="uplink",
                                      enable_pathloss=False,
                                      enable_shadow_fading=False,
                                      dtype=self.m_dtype)
        else:
            raise ValueError("[OFDMMIMO] Unsupported scenario type.")
        # Instantiate other building blocks
        self._binary_source = BinarySource()
        self._qam_source = QAMSource(self._num_bits_per_symbol,dtype=self.m_dtype)


        if self._coderate==1 and not self._simple_mimo:
            self._k = int(self._rg.num_data_symbols*self._num_bits_per_symbol)
            self._num_symbols = int(self._k/self._num_bits_per_symbol)
            self._hard_out = True
        elif self._coderate<1 and not self._simple_mimo:
            self._n = int(self._rg.num_data_symbols*self._num_bits_per_symbol) # Number of coded bits
            self._k = int(self._n*self._coderate)        # Number of information bits
            self._encoder = LDPC5GEncoder(self._k, self._n)
            self._decoder = LDPC5GDecoder(self._encoder)
            self._hard_out = False
            self._num_symbols = int(self._n/self._num_bits_per_symbol)

        if self._coderate==1 and self._simple_mimo:
            self._k = 192
            self._hard_out = True
            self._num_symbols = int(self._k/self._num_bits_per_symbol)
        elif self._coderate<1 and self._simple_mimo:
            self._n = 192 # Number of coded bits
            self._k = int(self._n*self._coderate) #i=14, k=553  # Number of information bits
            # self._k = 553 #i=14, k=553  # Number of information bits
            # print(f'coderate:{self._coderate}, {self._k/self._n }')
            self._num_symbols = int(self._n/self._num_bits_per_symbol)
            self._encoder = LDPC5GEncoder(self._k, self._n)
            self._decoder = LDPC5GDecoder(self._encoder)
            self._hard_out = False




        self._mapper = Mapper("qam", self._num_bits_per_symbol,dtype=self.m_dtype)
        self._rg_mapper = ResourceGridMapper(self._rg, dtype=self.m_dtype)

        self._ofdm_channel = OFDMChannel(self._channel_model, self._rg, add_awgn=True,
                                         normalize_channel=True, return_channel=True, dtype=self._dtype)

        self._remove_nulled_subcarriers = RemoveNulledSubcarriers(self._rg, dtype=self.m_dtype)
        self._ls_est = LSChannelEstimator(self._rg, interpolation_type="nn", dtype=self.m_dtype)
        self._lmmse_equ = eqz.LMMSEEqualizer(self._rg, self._sm, whiten_interference=False, dtype=self.m_dtype)
        self._demapper = Demapper("app", "qam", self._num_bits_per_symbol,hard_out=self._hard_out, dtype=self.m_dtype)
        # self._demapper = Demapper("maxlog", "qam", self._num_bits_per_symbol,hard_out=self._hard_out, dtype=self.m_dtype)

    def get_num_data_symbols(self):
        return self._rg.num_data_symbols.numpy()

    def new_topology(self, batch_size, min_ut_velocity=0.0, max_ut_velocity=0.0):
        """Set new topology"""
        topology = gen_topology(batch_size,
                                self._num_ut,
                                self._scenario,
                                min_ut_velocity=min_ut_velocity,
                                max_ut_velocity=max_ut_velocity,
                                dtype = self.m_dtype)

        self._channel_model.set_topology(*topology)



    def _extract_data_symbols(self, x):

        # x: [batch_size, num_tx, num_streams_per_ut, num_ofdm_symbols, fft_size]
        # to    [batch_size, num_tx, num_streams_per_ut, num_ofdm_symbols, num_effective_subcarriers]
        x = self._remove_nulled_subcarriers(x)

        # to [batch_size, num_tx, num_streams_per_ut, num_ofdm_symbols * num_effective_subcarriers]
        shape = x.shape
        x = tf.reshape(  x, (-1, shape[1], shape[2], shape[3]*shape[4])  )

        # [num_tx, num_streams, num_ofdm_symbols*num_effective_subcarriers,...
        #  ..., batch_size]
        x = tf.transpose(x,perm=[1,2,3,0])

        # Gather data symbols
        # [num_tx, num_streams, num_data_symbols, batch_size]
        x = tf.gather(x, self._data_ind, batch_dims=2, axis=2)

        # Put batch_dim first
        # [batch_size, num_tx, num_streams, num_data_symbols]
        x = tf.transpose(x, [3, 0, 1, 2])
        return x

    def demap_banshee(self, x_hat, no_eff, batch_size,num_symbols):

        # cast to self.m_dtype
        x_hat = tf.cast(x_hat,self.m_dtype)


        if self._simple_mimo:
            # x_hat [batch_size* num_symbols(k/M), num_ut]
            # to [batch_size, num_symbols(k/M), num_ut]
            # self._num_symbols
            x_hat = tf.reshape(x_hat,(batch_size,num_symbols,self._num_ut) )
            no_eff = tf.reshape(no_eff,(batch_size,num_symbols,self._num_ut) )
            

            # to [batch_size, num_ut,num_symbols(k/M)]
            x_hat = tf.transpose(x_hat,perm=[0,2,1])
            no_eff = tf.transpose(no_eff,perm=[0,2,1])
            

            if self._coderate==1:
                b_hat = self._demapper([x_hat, no_eff])
            else:
                llr = self._demapper([x_hat, no_eff])
                b_hat = self._decoder(llr)

            # b_hat: [batch_size, num_ut,num_bits(k)]   
             
        else:

            # no_eff [batch_size, num_tx, num_streams, num_data_symbols]
            # x_hat [ batch_size(N_batch * num_symbols), N_tx]
            # x_hat complex numpy: [batch_size*num_ofdm_sym*fft_size, num_tx*num_streams] 



            # reshape to [batch_size,num_ofdm_sym,fft_size, num_tx,num_streams]  
            x_hat = tf.reshape(  x_hat,(batch_size, self._num_ofdm_symbols, self._fft_size, self._num_tx,self._num_streams_per_tx) )

            # reshape to 
            # [batch_size, num_tx, num_streams_per_ut, num_ofdm_symbols, fft_size]
            x_hat = tf.transpose(  x_hat,perm=[0,3,4,1,2]  )

            # Extract data symbols
            # [batch_size, num_tx, num_streams, num_data_symbols]
            x_hat = self._extract_data_symbols(x_hat)

            if self._coderate==1:
                b_hat = self._demapper([x_hat, no_eff])
            else:
                llr = self._demapper([x_hat, no_eff])
                b_hat = self._decoder(llr)

            # x_hat: [batch_size, num_tx, num_streams, num_data_symbols]
            # reshape to [batch_size, num_data_symbols, num_tx, num_streams]
            x_hat = tf.transpose(x_hat,perm=[0,3,1,2])

            # reshape to 
            # [batch_size* num_data_symbols, num_tx* num_streams]
            shape = x_hat.shape
            x_hat = tf.reshape(x_hat,(-1,shape[2]*shape[3]))

        # print(f'[demapp bansshe]b_hat:{b_hat.shape}')

        return b_hat, x_hat
    def count_total_bit_error(self, b,b_hat):
        # print(f'[count err]b:{b.shape},b_hat:{b_hat.shape}')
        b = tf.cast(b,tf.float32)
        b_hat = tf.cast(b_hat,tf.float32)
        TBE = count_errors(b,b_hat)
        num_bits = b.shape.num_elements()
        ber = compute_ber(b,b_hat)


        return TBE.numpy(), num_bits, ber.numpy()


    # @tf.function # Run in graph mode. See the following guide: https://www.tensorflow.org/guide/function
    def call(self, batch_size, ebno_db, min_ut_velocity=0.0, max_ut_velocity=0.0):

        if self._simple_mimo:

            # b[batch_size, num_tx, num_bits]
            b = self._binary_source([batch_size, self._num_tx, self._k])
            if self._coderate==1:
                c = b
            else:
                c = self._encoder(b)            
            x = self._mapper(c)
            num_symbols = tf.shape(x)[-1]
            # self._num_symbols = tf.shape(x)[-1]
            # self._num_symbols = tf.keras.backend.get_value(tf.shape(x)[-1])

            # x: [batch_size,num_tx,num_symbols]
            # to [batch_size,num_symbols,num_tx]
            x = tf.transpose(x,perm=[0,2,1])
            shape = tf.shape(x)

            # to [batch_size*num_symbols,num_tx]
            x = tf.reshape(x, [-1, self._num_tx])
            no = ebnodb2no(ebno_db, self._num_bits_per_symbol, self._coderate)

            if self._scenario != 'awgn':
                no *= np.sqrt(self._num_bs_ant)
                no = tf.cast(no,self.m_dtype_real)                
                y_dt, h_dt_desired = self._channel_model([x, no])
            else:
                no = tf.cast(no,self.m_dtype_real)                  
                y_dt = self._channel_model((x, no))
                h = tf.eye(self._num_ut, dtype=self.m_dtype_real)
                h = tf.tile(tf.expand_dims(h, axis=0), [batch_size*num_symbols, 1, 1])
                h = tf.complex(h, tf.zeros_like(h),self.m_dtype)
                h_dt_desired = h

            # y: [batch_size*num_symbols, num_rx_ant]
            # H: [batch_size*num_symbols, num_rx_ant, num_tx_ant]

            s = tf.eye(self._num_bs_ant, self._num_bs_ant)
            s = tf.cast(s,self.m_dtype_real)
            s = no*s
            s = tf.complex(s, tf.cast(0.0,self.m_dtype_real))
            
            x_hat, no_eff = eqz.lmmse_equalizer(y_dt, h_dt_desired, s, whiten_interference=False)

            # [batch_size*num_symbols,num_tx]
            # to [batch_size,num_symbols,num_tx]
            x_hat = tf.reshape(x_hat, shape)
            x_data = tf.reshape(x, shape)
            no_eff = tf.reshape(no_eff, shape)


            # to [batch_size,num_tx,num_symbols]
            x_hat = tf.transpose(x_hat,perm=[0,2,1])
            no_eff = tf.transpose(no_eff,perm=[0,2,1])

            if self._coderate==1:
                b_hat = self._demapper([x_hat, no_eff])
            else:
                llr = self._demapper([x_hat, no_eff])
                b_hat = self._decoder(llr)


            # b [batch_size, num_tx, num_bits]
            # b_hat: [batch_size,num_tx,num_bits]
            # x_hat [batch_size,num_tx,num_symbols]




            # Reshape for Banshee
            
            
            # no_eff = tf.transpose(no_eff,perm=[0,2,1])
            # no_eff = tf.reshape(no_eff,(-1,self._num_ut) )

            # # x_hat:[batch_size,num_tx,num_symbols]
            # # to [batch_size, num_symbols(k/M), num_ut]
            x_hat = tf.transpose(x_hat,perm=[0,2,1])
            # to [batch_size* num_symbols(k/M), num_ut]
            x_hat = tf.reshape(x_hat,(-1,self._num_ut) )

            x_data = tf.transpose(x_data,perm=[0,2,1])
            x_data = tf.reshape(x_data,(-1,self._num_ut) )

            # H: [batch_size*num_symbols, num_rx_ant, num_tx_ant]
            # to [batch_size*num_symbols, num_rx_ant* num_tx_ant]
            h_dt_desired = tf.reshape(h_dt_desired,(-1,self._num_bs_ant*self._num_ut))

            # s: [num_rx_ant]
            s = tf.linalg.diag_part(s)
            # to: [batch_size*num_symbols, num_rx_ant]
            # dim0 = int(batch_size*self._k/self._num_bits_per_symbol)
            dim0 = batch_size*num_symbols
            s = tf.repeat(tf.expand_dims(s, axis=0),dim0,axis=0)



            # y: [batch_size*num_symbols, num_rx_ant]
            # H: [batch_size*num_symbols, num_rx_ant* num_tx_ant]
            # s: [batch_size*num_symbols, num_rx_ant]
            # x_hat: [batch_size* num_symbols(k/M), num_ut]

        else:

            self.new_topology(batch_size,min_ut_velocity=min_ut_velocity, max_ut_velocity=max_ut_velocity)
            no = ebnodb2no(ebno_db, self._num_bits_per_symbol, self._coderate, self._rg)

            # b: [batch_size, num_tx, num_stream_per_tx, k]
            b = self._binary_source([batch_size, self._num_tx, self._num_streams_per_tx, self._k])
            if self._coderate==1:
                c = b
            else:
                c = self._encoder(b)

            # x:[batch_size, num_tx, num_stream_per_tx, k/M]
            x = self._mapper(c)
            # self._num_symbols = tf.shape(x)[-1]
            num_symbols = tf.shape(x)[-1]

            # x_rg: [batch_size, num_tx, num_streams_per_ut, num_ofdm_symbols, fft_size]
            x_rg = self._rg_mapper(x)


            y, h = self._ofdm_channel([x_rg, no])
            if self._perfect_csi:
                h_hat = self._remove_nulled_subcarriers(h)
                err_var = 0.0
            else:
                h_hat, err_var = self._ls_est ([y, no])


            x_hat, no_eff, y_dt, h_dt_desired, s = self._lmmse_equ([y, h_hat, err_var, no])

            # y_dt [batch_size, num_rx, num_ofdm_symbols, num_effective_subcarriers, num_rx_ant]

            # x_hat [batch_size, num_tx, num_streams, num_data_symbols]

            # h_dt_desired [batch_size, num_rx, num_ofdm_symbols, num_effective_subcarriers,..
            #  ..., num_rx_ant, num_streams_per_rx(num_Interfering_streams_per_rx)]

            # s: [batch_size, num_rx, num_ofdm_syms, fft_size, num_rx_ant, num_rx_ant]

            # print(f'x_hat:{x_hat.shape}, no_eff:{no_eff.shape}, s:{s.shape}')

            if self._coderate==1:
                b_hat = self._demapper([x_hat, no_eff])
            else:
                llr = self._demapper([x_hat, no_eff])
                b_hat = self._decoder(llr)

            # b_hat: [batch_size, num_tx, num_streams, k=num_data_symbols*M]
            # b [batch_size, num_tx, num_stream_per_tx, k]
            ber = compute_ber(b,tf.cast(b_hat,tf.float32))

            # num_rx>1 not considered (TODO)
            # --------- reshape for banshee -----------


            # [batch_size, num_rx, num_ofdm_symbols, num_effective_subcarriers, num_rx_ant]
            # TO [batch_size* num_rx* num_ofdm_symbols* num_effective_subcarriers, num_rx_ant]
            y_dt = tf.reshape(y_dt,(-1,self._num_bs_ant))



            # TO [batch_size* num_rx* num_ofdm_symbols* num_effective_subcarriers,..
            #  ..., num_rx_ant, num_streams_per_rx(num_Interfering_streams_per_rx)]
            h_shape = tf.shape(h_dt_desired)
            h_dt_desired = tf.reshape(h_dt_desired,(-1,h_shape[4],h_shape[5]))


            #TO [batch_size* num_rx* num_ofdm_symbols* num_effective_subcarriers,..
            #  ..., num_rx_ant* num_streams_per_rx(num_Interfering_streams_per_rx)]
            h_dt_desired = tf.reshape(h_dt_desired,(-1,h_shape[4]*h_shape[5]))

            # s: [batch_size, num_rx, num_ofdm_syms, fft_size, num_rx_ant, num_rx_ant]
            # to [batch_size, num_rx, num_ofdm_syms, fft_size, num_rx_ant]
            s = tf.linalg.diag_part(s)
            # to [batch_size* num_rx* num_ofdm_syms* fft_size, num_rx_ant]
            s = tf.reshape(s, (-1,self._num_bs_ant))



            # x: extract data symbols
            # [batch_size, num_tx, num_streams, num_data_symbols]
            x_data = self._extract_data_symbols(x=x_rg)

            # x_hat: [batch_size, num_tx, num_streams, num_data_symbols]
            # reshape to [batch_size, num_data_symbols, num_tx, num_streams]
            x_hat = tf.transpose(x_hat,perm=[0,3,1,2])
            x_data = tf.transpose(x_data,perm=[0,3,1,2])



            # reshape to 
            # [batch_size* num_data_symbols, num_tx* num_streams]
            shape = x_hat.shape
            x_hat = tf.reshape(x_hat,(-1,shape[2]*shape[3]))
            x_data = tf.reshape(x_data,(-1,shape[2]*shape[3]))


            
        
        # ----------- End Simple MIMO or OFDM -----------
        # print(f'y_dt:{y_dt.shape}, h_dt_desired:{h_dt_desired.shape}, x_data:{x_data.shape}, x_hat:{x_hat.shape}, s:{s.shape}, no_eff:{no_eff.shape}')
        # print(f'[call]b:{b.shape},b_hat:{b_hat.shape}')
        no = tf.cast(no,self.m_dtype_real)
        no_db = 10*tf.math.log(no)/tf.math.log(tf.constant(10.0,self.m_dtype_real))

        return b, b_hat, x_data, x_hat, y_dt, h_dt_desired, s, no_eff, num_symbols, no_db






