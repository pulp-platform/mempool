/* Copyright (C) 2017 ETH Zurich, University of Bologna
 * All rights reserved.
 *
 * This code is under development and not yet released to the public.
 * Until it is released, the code is under the copyright of ETH Zurich and
 * the University of Bologna, and may contain confidential and/or unpublished
 * work. Any reuse/redistribution is strictly forbidden without written
 * permission from ETH Zurich.
 *
 * Bug fixes and contributions will eventually be released under the
 * SolderPad open hardware license in the context of the PULP platform
 * (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
 * University of Bologna.
 */

// issue write requests with linear data
task FILL_LINEAR
(
  input  logic [31:0]                  address_base,
  input  logic [AXI4_WDATA_WIDTH-1:0]  fill_pattern,
  input  logic [7:0]                   cmd_id = 'b0,
  input  logic [15:0]                  transfer_count,
  input  string                        transfer_type
);

begin

  int unsigned                         count_local_AW;
  int unsigned                         count_local_W;
  logic   [31:0][AXI4_WDATA_WIDTH-1:0] local_wdata;
  logic   [AXI_NUMBYTES-1:0]           local_be;

  case(transfer_type)

  "4_BYTE" :
  begin
    fork
      for ( count_local_AW = 0; count_local_AW < transfer_count; count_local_AW++)
      begin
        ST4_AW ( .id({cmd_id[3:0], count_local_AW[3:0]}), .address(address_base + count_local_AW*4  ), .user(SRC_ID) );
      end

      for ( count_local_W = 0; count_local_W < transfer_count; count_local_W++)
      begin
        local_wdata[0] = fill_pattern + count_local_W*4;
        if(count_local_W % 2)
              local_be = {  {AXI_NUMBYTES/2{1'b1}},{AXI_NUMBYTES/2{1'b0}}  };
        else
              local_be = {  {AXI_NUMBYTES/2{1'b0}},{AXI_NUMBYTES/2{1'b1}}  };
        ST4_DW ( .wdata(local_wdata[0]), .be('1), .user(SRC_ID) );
      end
    join
  end


  "8_BYTE" :
  begin
    fork
      for ( count_local_AW = 0; count_local_AW < transfer_count; count_local_AW++)
      begin
        ST8_AW ( .id({cmd_id[3:0], count_local_AW[3:0]}), .address(address_base + count_local_AW*8 ), .user(SRC_ID) );
      end

      for ( count_local_W = 0; count_local_W < transfer_count; count_local_W++)
      begin
        local_wdata[0] = fill_pattern + count_local_W*8 + 0 ;
        ST8_DW ( .wdata(local_wdata[0]), .be('1), .user(SRC_ID) );
      end
    join
  end

  "16_BYTE" :
  begin
    fork
      for ( count_local_AW = 0; count_local_AW < transfer_count; count_local_AW++)
      begin
        ST16_AW ( .id({cmd_id[3:0], count_local_AW[3:0]}), .address(address_base + count_local_AW*16 ),  .user(SRC_ID) );
      end

      for ( count_local_W = 0; count_local_W < transfer_count; count_local_W++)
      begin
        local_wdata[0] = fill_pattern + count_local_W*16 + 0 ;
        local_wdata[1] = fill_pattern + count_local_W*16 + 8 ;
        ST16_DW ( .wdata(local_wdata[1:0]), .be('1), .user(SRC_ID) );
      end
    join
  end

  "24_BYTE" :
  begin
    fork
      for ( count_local_AW = 0; count_local_AW < transfer_count; count_local_AW++)
      begin
        ST24_AW ( .id({cmd_id[3:0], count_local_AW[3:0]}), .address(address_base + count_local_AW*24 ),  .user(SRC_ID) );
      end

      for ( count_local_W = 0; count_local_W < transfer_count; count_local_W++)
      begin
        local_wdata[0] = fill_pattern + count_local_W*24 + 0 ;
        local_wdata[1] = fill_pattern + count_local_W*24 + 8 ;
        local_wdata[2] = fill_pattern + count_local_W*24 + 16 ;
        ST24_DW ( .wdata(local_wdata[2:0]), .be('1), .user(SRC_ID) );
      end
    join
  end

  "32_BYTE" :
  begin
    fork
      for ( count_local_AW = 0; count_local_AW < transfer_count; count_local_AW++)
      begin
        ST32_AW ( .id({cmd_id[3:0], count_local_AW[3:0]}), .address(address_base + count_local_AW*32 ), .user(SRC_ID) );
      end

      for ( count_local_W = 0; count_local_W < transfer_count; count_local_W++)
      begin
        local_wdata[0] = fill_pattern + count_local_W*32 + 0 ;
        local_wdata[1] = fill_pattern + count_local_W*32 + 8 ;
        local_wdata[2] = fill_pattern + count_local_W*32 + 16 ;
        local_wdata[3] = fill_pattern + count_local_W*32 + 24 ;
        ST32_DW ( .wdata(local_wdata[3:0]), .be('1), .user(SRC_ID) );
      end
    join
  end

  "64_BYTE" :
  begin
    fork
      for ( count_local_AW = 0; count_local_AW < transfer_count; count_local_AW++)
      begin
        ST64_AW ( .id({cmd_id[3:0], count_local_AW[3:0]}), .address(address_base + count_local_AW*64 ), .user(SRC_ID) );
      end

      for ( count_local_W = 0; count_local_W < transfer_count; count_local_W++)
      begin
        local_wdata[0] = fill_pattern + count_local_W*64 + 0 ;
        local_wdata[1] = fill_pattern + count_local_W*64 + 8 ;
        local_wdata[2] = fill_pattern + count_local_W*64 + 16 ;
        local_wdata[3] = fill_pattern + count_local_W*64 + 24 ;
        local_wdata[4] = fill_pattern + count_local_W*64 + 32 ;
        local_wdata[5] = fill_pattern + count_local_W*64 + 40 ;
        local_wdata[6] = fill_pattern + count_local_W*64 + 48 ;
        local_wdata[7] = fill_pattern + count_local_W*64 + 56 ;
        ST64_DW ( .wdata(local_wdata[7:0]), .be('1), .user(SRC_ID) );
      end
    join
  end // case: "64_BYTE"

  "256_BYTE" :
  begin
    fork
      for ( count_local_AW = 0; count_local_AW < transfer_count; count_local_AW++)
      begin
        ST256_AW ( .id({cmd_id[3:0], count_local_AW[3:0]}), .address(address_base + count_local_AW*256 ), .user(SRC_ID) );
      end

      for ( count_local_W = 0; count_local_W < transfer_count; count_local_W++)
      begin
        local_wdata[0]  = fill_pattern + count_local_W*256 + 0 ;
        local_wdata[1]  = fill_pattern + count_local_W*256 + 8 ;
        local_wdata[2]  = fill_pattern + count_local_W*256 + 16 ;
        local_wdata[3]  = fill_pattern + count_local_W*256 + 24 ;
        local_wdata[4]  = fill_pattern + count_local_W*256 + 32 ;
        local_wdata[5]  = fill_pattern + count_local_W*256 + 40 ;
        local_wdata[6]  = fill_pattern + count_local_W*256 + 48 ;
        local_wdata[7]  = fill_pattern + count_local_W*256 + 56 ;
        local_wdata[8]  = fill_pattern + count_local_W*256 + 64 ;
        local_wdata[9]  = fill_pattern + count_local_W*256 + 72 ;
        local_wdata[10] = fill_pattern + count_local_W*256 + 80 ;
        local_wdata[11] = fill_pattern + count_local_W*256 + 88 ;
        local_wdata[12] = fill_pattern + count_local_W*256 + 96 ;
        local_wdata[13] = fill_pattern + count_local_W*256 + 104 ;
        local_wdata[14] = fill_pattern + count_local_W*256 + 112 ;
        local_wdata[15] = fill_pattern + count_local_W*256 + 120 ;
        local_wdata[16] = fill_pattern + count_local_W*256 + 128 ;
        local_wdata[17] = fill_pattern + count_local_W*256 + 136 ;
        local_wdata[18] = fill_pattern + count_local_W*256 + 144 ;
        local_wdata[19] = fill_pattern + count_local_W*256 + 152 ;
        local_wdata[20] = fill_pattern + count_local_W*256 + 160 ;
        local_wdata[21] = fill_pattern + count_local_W*256 + 168 ;
        local_wdata[22] = fill_pattern + count_local_W*256 + 176 ;
        local_wdata[23] = fill_pattern + count_local_W*256 + 184 ;
        local_wdata[24] = fill_pattern + count_local_W*256 + 192 ;
        local_wdata[25] = fill_pattern + count_local_W*256 + 200 ;
        local_wdata[26] = fill_pattern + count_local_W*256 + 208 ;
        local_wdata[27] = fill_pattern + count_local_W*256 + 216 ;
        local_wdata[28] = fill_pattern + count_local_W*256 + 224 ;
        local_wdata[29] = fill_pattern + count_local_W*256 + 232 ;
        local_wdata[30] = fill_pattern + count_local_W*256 + 240 ;
        local_wdata[31] = fill_pattern + count_local_W*256 + 248 ;
        ST256_DW ( .wdata(local_wdata[31:0]), .be('1), .user(SRC_ID) );
      end
    join
  end // case: "64_BYTE"

  default:
    begin
      $error("Unknown transfer type. Please specify the size of the requested transfers.");
    end

  endcase

end
endtask

// issue read requests
task READ_LINEAR
(
  input  logic [31:0]  address_base,
  input  logic [7:0]   cmd_id = 'b0,
  input  logic [15:0]  transfer_count,
  input  string        transfer_type
);

begin

  integer              count_local_AR;
  logic   [7:0][31:0]  local_wdata;

  case(transfer_type)

    "4_BYTE" :
    begin
      for ( count_local_AR = 0; count_local_AR < transfer_count; count_local_AR++)
      begin
        LD4 ( .id      ( {cmd_id[3:0], count_local_AR[3:0]} ),
              .address ( address_base + count_local_AR*4    ),
              .user    ( SRC_ID                             )
            );
      end
    end

    "8_BYTE" :
    begin
      for ( count_local_AR = 0; count_local_AR < transfer_count; count_local_AR++)
      begin
        LD8 ( .id      ( {cmd_id[3:0], count_local_AR[3:0]} ),
              .address ( address_base + count_local_AR*8    ),
              .user    ( SRC_ID                             )
            );
      end
    end

    "16_BYTE" :
    begin
      for ( count_local_AR = 0; count_local_AR < transfer_count; count_local_AR++)
      begin
        LD16 ( .id     ( {cmd_id[3:0], count_local_AR[3:0]} ),
               .address( address_base + count_local_AR*16   ),
               .user   ( SRC_ID                             )
              );
      end
    end

    "24_BYTE" :
    begin
      for ( count_local_AR = 0; count_local_AR < transfer_count; count_local_AR++)
      begin
        LD24 ( .id     ( {cmd_id[3:0], count_local_AR[3:0]} ),
               .address( address_base + count_local_AR*24   ),
               .user   ( SRC_ID                             )
              );
      end
    end

    "32_BYTE" :
    begin
      for ( count_local_AR = 0; count_local_AR < transfer_count; count_local_AR++)
      begin
        LD32 ( .id     ( {cmd_id[3:0], count_local_AR[3:0]} ),
               .address( address_base + count_local_AR*32   ),
               .user   ( SRC_ID                             )
             );
      end
    end

    "64_BYTE" :
    begin
      for ( count_local_AR = 0; count_local_AR < transfer_count; count_local_AR++)
      begin
        LD64 ( .id      ( {cmd_id[3:0], count_local_AR[3:0]} ),
               .address ( address_base + count_local_AR*64   ),
               .user    ( SRC_ID                             )
             );
      end
    end

    "256_BYTE" :
    begin
      for ( count_local_AR = 0; count_local_AR < transfer_count; count_local_AR++)
      begin
        LD256 ( .id      ( {cmd_id[3:0], count_local_AR[3:0]} ),
                .address ( address_base + count_local_AR*256  ),
                .user    ( SRC_ID                             )
              );
      end
    end

    default:
      begin
        $error("Unknown transfer type. Please specify the size of the requested transfers.");
      end

  endcase

end
endtask

// issue read quests and check the returned data
task CHECK_LINEAR
(
  input  logic [31:0]                  address_base,
  input  logic [7:0]                   cmd_id = 'b0,
  input  logic [15:0]                  transfer_count,
  input  string                        transfer_type,
  input  logic [AXI4_WDATA_WIDTH-1:0]  check_pattern
);

struct
{
  logic [AXI4_ID_WIDTH-1:0]            id;
  logic [AXI4_ADDRESS_WIDTH-1:0]       addr;
  integer                              xfer_count;
  integer                              xfer_done;
  integer                              xfer_out;
} check_linear_queue[$], AR_temp_slot, R_temp_slot;

integer                                i_queue, queue_found;

begin

  integer                              count_local_AR, count_local_R;
  logic   [7:0][AXI4_WDATA_WIDTH-1:0]  local_wdata;

  automatic int unsigned local_PASS = 0;
  automatic int unsigned local_FAIL = 0;

  integer                              count_beat;
  automatic int unsigned               n_beats_failed;

  case(transfer_type)

      "4_BYTE" :
      begin
        // push to queue
        for ( count_local_AR = 0; count_local_AR < transfer_count; count_local_AR++) begin
          AR_temp_slot.id         = {cmd_id[3:0], count_local_AR[3:0]};
          AR_temp_slot.addr       = address_base + count_local_AR*4;
          AR_temp_slot.xfer_count = count_local_AR;
          AR_temp_slot.xfer_done  = 0;
          AR_temp_slot.xfer_out   = 0;

          check_linear_queue.push_back(AR_temp_slot);
        end

        fork
          // issue the read request
          for ( count_local_AR = 0; count_local_AR < transfer_count; count_local_AR++) begin
            if ( (check_linear_queue[count_local_AR].xfer_done == 0) &&
                 (check_linear_queue[count_local_AR].xfer_out  == 0) ) begin
              check_linear_queue[count_local_AR].xfer_out = 1;
              LD4   ( .id     (check_linear_queue[count_local_AR].id),
                      .address(check_linear_queue[count_local_AR].addr),
                      .user   (SRC_ID) );
            end
          end

          // check the read responses
          for ( count_local_R = 0; count_local_R < transfer_count; count_local_R++) begin

            @(IncomingRead);

            // find the proper transaction in list of outstanding ones
            queue_found = 0;
            for (i_queue=0; i_queue<check_linear_queue.size(); i_queue++) begin
              if ( (check_linear_queue[i_queue].id == RID) &&
                   (check_linear_queue[i_queue].xfer_done == 0) &&
                   (check_linear_queue[i_queue].xfer_out  == 1) ) begin
                R_temp_slot = check_linear_queue[i_queue];
                queue_found = 1;
                break;
              end
            end
            if (queue_found == 0) begin
              $error("No read transaction outstanding with ID = %x ", RID);
            end

            // check the data
            n_beats_failed = 0;
            for (count_beat = 0; count_beat < 1; count_beat++) begin

              if (count_beat > 0) begin
                @(IncomingRead);
              end

              if ( (RRESP == 1'b00) &&
                   (RDATA != check_pattern + R_temp_slot.xfer_count*4 + count_beat*8 ) ) begin
                $error("RDATA ERROR: got %x != %x [expected]... Address is %h",
                  RDATA ,
                  check_pattern + R_temp_slot.xfer_count*4 + count_beat*8,
                  address_base  + R_temp_slot.xfer_count*4 + count_beat*8);
                n_beats_failed++;
              //end else begin
              //  $display("Finished beat %d from address %x correctly. ID = %x.",
              //  count_beat, address_base + R_temp_slot.xfer_count*64 + count_beat*8, RID);
              end
            end

            // remove finished transactions from queue
            if (queue_found == 1) begin
              check_linear_queue[i_queue].xfer_done = 1;

              if (n_beats_failed > 0) begin
                local_FAIL++;
              end else begin
                //$display("Finished transfer from address %x with ID %x correctly.",
                //address_base + R_temp_slot.xfer_count*64, RID);
                local_PASS++;
              end
            end
          end
        join

        // remove all requests from the queue
        for ( count_local_AR = 0; count_local_AR < transfer_count; count_local_AR++) begin
          check_linear_queue.pop_front();
        end
      end // 4 Bytes

      "8_BYTE" :
      begin
        // push to queue
        for ( count_local_AR = 0; count_local_AR < transfer_count; count_local_AR++) begin
          AR_temp_slot.id         = {cmd_id[3:0], count_local_AR[3:0]};
          AR_temp_slot.addr       = address_base + count_local_AR*8;
          AR_temp_slot.xfer_count = count_local_AR;
          AR_temp_slot.xfer_done  = 0;
          AR_temp_slot.xfer_out   = 0;

          check_linear_queue.push_back(AR_temp_slot);
        end

        fork
          // issue the read request
          for ( count_local_AR = 0; count_local_AR < transfer_count; count_local_AR++) begin
            if ( (check_linear_queue[count_local_AR].xfer_done == 0) &&
                 (check_linear_queue[count_local_AR].xfer_out  == 0) ) begin
              check_linear_queue[count_local_AR].xfer_out = 1;
              LD8   ( .id     (check_linear_queue[count_local_AR].id),
                      .address(check_linear_queue[count_local_AR].addr),
                      .user   (SRC_ID) );
            end
          end

          // check the read responses
          for ( count_local_R = 0; count_local_R < transfer_count; count_local_R++) begin

            @(IncomingRead);

            // find the proper transaction in list of outstanding ones
            queue_found = 0;
            for (i_queue=0; i_queue<check_linear_queue.size(); i_queue++) begin
              if ( (check_linear_queue[i_queue].id == RID) &&
                   (check_linear_queue[i_queue].xfer_done == 0) &&
                   (check_linear_queue[i_queue].xfer_out  == 1) ) begin
                R_temp_slot = check_linear_queue[i_queue];
                queue_found = 1;
                break;
              end
            end
            if (queue_found == 0) begin
              $error("No read transaction outstanding with ID = %x ", RID);
            end

            // check the data
            n_beats_failed = 0;
            for (count_beat = 0; count_beat < 1; count_beat++) begin

              if (count_beat > 0) begin
                @(IncomingRead);
              end

              if ( (RRESP == 1'b00) &&
                   (RDATA != check_pattern + R_temp_slot.xfer_count*8 + count_beat*8 ) ) begin
                $error("RDATA ERROR: got %x != %x [expected]... Address is %h",
                  RDATA ,
                  check_pattern + R_temp_slot.xfer_count*8 + count_beat*8,
                  address_base  + R_temp_slot.xfer_count*8 + count_beat*8);
                n_beats_failed++;
              //end else begin
              //  $display("Finished beat %d from address %x correctly. ID = %x.",
              //  count_beat, address_base + R_temp_slot.xfer_count*8 + count_beat*8, RID);
              end
            end

            // remove finished transactions from queue
            if (queue_found == 1) begin
              check_linear_queue[i_queue].xfer_done = 1;

              if (n_beats_failed > 0) begin
                local_FAIL++;
              end else begin
                //$display("Finished transfer from address %x with ID %x correctly.",
                //address_base + R_temp_slot.xfer_count*8, RID);
                local_PASS++;
              end
            end
          end
        join

        // remove all requests from the queue
        for ( count_local_AR = 0; count_local_AR < transfer_count; count_local_AR++) begin
          check_linear_queue.pop_front();
        end
      end // 8 Bytes

      "16_BYTE" :
      begin
        // push to queue
        for ( count_local_AR = 0; count_local_AR < transfer_count; count_local_AR++) begin
          AR_temp_slot.id         = {cmd_id[3:0], count_local_AR[3:0]};
          AR_temp_slot.addr       = address_base + count_local_AR*16;
          AR_temp_slot.xfer_count = count_local_AR;
          AR_temp_slot.xfer_done  = 0;
          AR_temp_slot.xfer_out   = 0;

          check_linear_queue.push_back(AR_temp_slot);
        end

        fork
          // issue the read request
          for ( count_local_AR = 0; count_local_AR < transfer_count; count_local_AR++) begin
            if ( (check_linear_queue[count_local_AR].xfer_done == 0) &&
                 (check_linear_queue[count_local_AR].xfer_out  == 0) ) begin
              check_linear_queue[count_local_AR].xfer_out = 1;
              LD16  ( .id     (check_linear_queue[count_local_AR].id),
                      .address(check_linear_queue[count_local_AR].addr),
                      .user   (SRC_ID) );
            end
          end

          // check the read responses
          for ( count_local_R = 0; count_local_R < transfer_count; count_local_R++) begin

            @(IncomingRead);

            // find the proper transaction in list of outstanding ones
            queue_found = 0;
            for (i_queue=0; i_queue<check_linear_queue.size(); i_queue++) begin
              if ( (check_linear_queue[i_queue].id == RID) &&
                   (check_linear_queue[i_queue].xfer_done == 0) &&
                   (check_linear_queue[i_queue].xfer_out  == 1) ) begin
                R_temp_slot = check_linear_queue[i_queue];
                queue_found = 1;
                break;
              end
            end
            if (queue_found == 0) begin
              $error("No read transaction outstanding with ID = %x ", RID);
            end

            // check the data
            n_beats_failed = 0;
            for (count_beat = 0; count_beat < 2; count_beat++) begin

              if (count_beat > 0) begin
                @(IncomingRead);
              end

              if ( (RRESP == 1'b00) &&
                   (RDATA != check_pattern + R_temp_slot.xfer_count*16 + count_beat*8 ) ) begin
                $error("RDATA ERROR: got %x != %x [expected]... Address is %h",
                  RDATA ,
                  check_pattern + R_temp_slot.xfer_count*16 + count_beat*8,
                  address_base  + R_temp_slot.xfer_count*16 + count_beat*8);
                n_beats_failed++;
              //end else begin
              //  $display("Finished beat %d from address %x correctly. ID = %x.",
              //  count_beat, address_base + R_temp_slot.xfer_count*16 + count_beat*8, RID);
              end
            end

            // remove finished transactions from queue
            if (queue_found == 1) begin
              check_linear_queue[i_queue].xfer_done = 1;

              if (n_beats_failed > 0) begin
                local_FAIL++;
              end else begin
                //$display("Finished transfer from address %x with ID %x correctly.",
                //address_base + R_temp_slot.xfer_count*16, RID);
                local_PASS++;
              end
            end
          end
        join

        // remove all requests from the queue
        for ( count_local_AR = 0; count_local_AR < transfer_count; count_local_AR++) begin
          check_linear_queue.pop_front();
        end
      end // 16 Bytes

      "32_BYTE" :
      begin
        // push to queue
        for ( count_local_AR = 0; count_local_AR < transfer_count; count_local_AR++) begin
          AR_temp_slot.id         = {cmd_id[3:0], count_local_AR[3:0]};
          AR_temp_slot.addr       = address_base + count_local_AR*32;
          AR_temp_slot.xfer_count = count_local_AR;
          AR_temp_slot.xfer_done  = 0;
          AR_temp_slot.xfer_out   = 0;

          check_linear_queue.push_back(AR_temp_slot);
        end

        fork
          // issue the read request
          for ( count_local_AR = 0; count_local_AR < transfer_count; count_local_AR++) begin
            if ( (check_linear_queue[count_local_AR].xfer_done == 0) &&
                 (check_linear_queue[count_local_AR].xfer_out  == 0) ) begin
              check_linear_queue[count_local_AR].xfer_out = 1;
              LD32  ( .id     (check_linear_queue[count_local_AR].id),
                      .address(check_linear_queue[count_local_AR].addr),
                      .user   (SRC_ID) );
            end
          end

          // check the read responses
          for ( count_local_R = 0; count_local_R < transfer_count; count_local_R++) begin

            @(IncomingRead);

            // find the proper transaction in list of outstanding ones
            queue_found = 0;
            for (i_queue=0; i_queue<check_linear_queue.size(); i_queue++) begin
              if ( (check_linear_queue[i_queue].id == RID) &&
                   (check_linear_queue[i_queue].xfer_done == 0) &&
                   (check_linear_queue[i_queue].xfer_out  == 1) ) begin
                R_temp_slot = check_linear_queue[i_queue];
                queue_found = 1;
                break;
              end
            end
            if (queue_found == 0) begin
              $error("No read transaction outstanding with ID = %x ", RID);
            end

            // check the data
            n_beats_failed = 0;
            for (count_beat = 0; count_beat < 4; count_beat++) begin

              if (count_beat > 0) begin
                @(IncomingRead);
              end

              if ( (RRESP == 1'b00) &&
                   (RDATA != check_pattern + R_temp_slot.xfer_count*32 + count_beat*8 ) ) begin
                $error("RDATA ERROR: got %x != %x [expected]... Address is %h",
                  RDATA ,
                  check_pattern + R_temp_slot.xfer_count*32 + count_beat*8,
                  address_base  + R_temp_slot.xfer_count*32 + count_beat*8);
                n_beats_failed++;
              //end else begin
              //  $display("Finished beat %d from address %x correctly. ID = %x.",
              //  count_beat, address_base + R_temp_slot.xfer_count*32 + count_beat*8, RID);
              end
            end

            // remove finished transactions from queue
            if (queue_found == 1) begin
              check_linear_queue[i_queue].xfer_done = 1;

              if (n_beats_failed > 0) begin
                local_FAIL++;
              end else begin
                //$display("Finished transfer from address %x with ID %x correctly.",
                //address_base + R_temp_slot.xfer_count*32, RID);
                local_PASS++;
              end
            end
          end
        join

        // remove all requests from the queue
        for ( count_local_AR = 0; count_local_AR < transfer_count; count_local_AR++) begin
          check_linear_queue.pop_front();
        end
      end // 32 Bytes

      "64_BYTE" :
      begin
        // push to queue
        for ( count_local_AR = 0; count_local_AR < transfer_count; count_local_AR++) begin
          AR_temp_slot.id         = {cmd_id[3:0], count_local_AR[3:0]};
          AR_temp_slot.addr       = address_base + count_local_AR*64;
          AR_temp_slot.xfer_count = count_local_AR;
          AR_temp_slot.xfer_done  = 0;
          AR_temp_slot.xfer_out   = 0;

          check_linear_queue.push_back(AR_temp_slot);
        end

        fork
          // issue the read request
          for ( count_local_AR = 0; count_local_AR < transfer_count; count_local_AR++) begin
            if ( (check_linear_queue[count_local_AR].xfer_done == 0) &&
                 (check_linear_queue[count_local_AR].xfer_out  == 0) ) begin
              check_linear_queue[count_local_AR].xfer_out = 1;
              LD64  ( .id     (check_linear_queue[count_local_AR].id),
                      .address(check_linear_queue[count_local_AR].addr),
                      .user   (SRC_ID) );
            end
          end

          // check the read responses
          for ( count_local_R = 0; count_local_R < transfer_count; count_local_R++) begin

            @(IncomingRead);

            // find the proper transaction in list of outstanding ones
            queue_found = 0;
            for (i_queue=0; i_queue<check_linear_queue.size(); i_queue++) begin
              if ( (check_linear_queue[i_queue].id == RID) &&
                   (check_linear_queue[i_queue].xfer_done == 0) &&
                   (check_linear_queue[i_queue].xfer_out  == 1) ) begin
                R_temp_slot = check_linear_queue[i_queue];
                queue_found = 1;
                break;
              end
            end
            if (queue_found == 0) begin
              $error("No read transaction outstanding with ID = %x ", RID);
            end

            // check the data
            n_beats_failed = 0;
            for (count_beat = 0; count_beat < 8; count_beat++) begin

              if (count_beat > 0) begin
                @(IncomingRead);
              end

              if ( (RRESP == 1'b00) &&
                   (RDATA != check_pattern + R_temp_slot.xfer_count*64 + count_beat*8 ) ) begin
                $error("RDATA ERROR: got %x != %x [expected]... Address is %h",
                  RDATA ,
                  check_pattern + R_temp_slot.xfer_count*64 + count_beat*8,
                  address_base  + R_temp_slot.xfer_count*64 + count_beat*8);
                n_beats_failed++;
              //end else begin
              //  $display("Finished beat %d from address %x correctly. ID = %x.",
              //  count_beat, address_base + R_temp_slot.xfer_count*64 + count_beat*8, RID);
              end
            end

            // remove finished transactions from queue
            if (queue_found == 1) begin
              check_linear_queue[i_queue].xfer_done = 1;

              if (n_beats_failed > 0) begin
                local_FAIL++;
              end else begin
                //$display("Finished transfer from address %x with ID %x correctly.",
                //address_base + R_temp_slot.xfer_count*64, RID);
                local_PASS++;
              end
            end
          end
        join

        // remove all requests from the queue
        for ( count_local_AR = 0; count_local_AR < transfer_count; count_local_AR++) begin
          check_linear_queue.pop_front();
        end
      end // 64 Bytes

      "256_BYTE" :
      begin
        // push to queue
        for ( count_local_AR = 0; count_local_AR < transfer_count; count_local_AR++) begin
          AR_temp_slot.id         = {cmd_id[3:0], count_local_AR[3:0]};
          AR_temp_slot.addr       = address_base + count_local_AR*256;
          AR_temp_slot.xfer_count = count_local_AR;
          AR_temp_slot.xfer_done  = 0;
          AR_temp_slot.xfer_out   = 0;

          check_linear_queue.push_back(AR_temp_slot);
        end

        fork
          // issue the read request
          for ( count_local_AR = 0; count_local_AR < transfer_count; count_local_AR++) begin
            if ( (check_linear_queue[count_local_AR].xfer_done == 0) &&
                 (check_linear_queue[count_local_AR].xfer_out  == 0) ) begin
              check_linear_queue[count_local_AR].xfer_out = 1;
              LD256 ( .id     (check_linear_queue[count_local_AR].id),
                      .address(check_linear_queue[count_local_AR].addr),
                      .user   (SRC_ID) );
            end
          end

          // check the read responses
          for ( count_local_R = 0; count_local_R < transfer_count; count_local_R++) begin

            @(IncomingRead);

            // find the proper transaction in list of outstanding ones
            queue_found = 0;
            for (i_queue=0; i_queue<check_linear_queue.size(); i_queue++) begin
              if ( (check_linear_queue[i_queue].id == RID) &&
                   (check_linear_queue[i_queue].xfer_done == 0) &&
                   (check_linear_queue[i_queue].xfer_out  == 1) ) begin
                R_temp_slot = check_linear_queue[i_queue];
                queue_found = 1;
                break;
              end
            end
            if (queue_found == 0) begin
              $error("No read transaction outstanding with ID = %x ", RID);
            end

            // check the data
            n_beats_failed = 0;
            for (count_beat = 0; count_beat < 32; count_beat++) begin

              if (count_beat > 0) begin
                @(IncomingRead);
              end

              if ( (RRESP == 1'b00) &&
                   (RDATA != check_pattern + R_temp_slot.xfer_count*256 + count_beat*8 ) ) begin
                $error("RDATA ERROR: got %x != %x [expected]... Address is %h",
                  RDATA ,
                  check_pattern + R_temp_slot.xfer_count*256 + count_beat*8,
                  address_base  + R_temp_slot.xfer_count*256 + count_beat*8);
                n_beats_failed++;
              //end else begin
              //  $display("Finished beat %d from address %x correctly. ID = %x.",
              //  count_beat, address_base + R_temp_slot.xfer_count*256 + count_beat*8, RID);
              end
            end

            // remove finished transactions from queue
            if (queue_found == 1) begin
              check_linear_queue[i_queue].xfer_done = 1;

              if (n_beats_failed > 0) begin
                local_FAIL++;
              end else begin
                //$display("Finished transfer from address %x with ID %x correctly.",
                //address_base + R_temp_slot.xfer_count*256, RID);
                local_PASS++;
              end
            end
          end
        join

        // remove all requests from the queue
        for ( count_local_AR = 0; count_local_AR < transfer_count; count_local_AR++) begin
          check_linear_queue.pop_front();
        end
      end // 256 Bytes

      default:
        begin
          $error("Unknown transfer type. Please specify the size of the requested transfers.");
        end

  endcase

  PASS = PASS + local_PASS;
  FAIL = FAIL + local_FAIL;

end
endtask

// issue random writes with random data
task FILL_RANDOM
(
  input  logic [31:0]                 address_base,
  input  logic [AXI4_WDATA_WIDTH-1:0] fill_pattern,
  input  logic [7:0]                  cmd_id = 'b0,
  input  logic [15:0]                 transfer_count,
  input  string                       transfer_type
);
  parameter                           RANDOM_ADDR_BITS = 6;

begin

  integer                             count_local_AW;
  integer                             count_local_W;
  logic   [7:0][AXI4_WDATA_WIDTH-1:0] local_wdata;
  logic   [AXI_NUMBYTES-1:0]          local_be;
  logic   [31:0]                      local_addr;

  case(transfer_type)

  "4_BYTE" :
  begin
    fork
      for ( count_local_AW = 0; count_local_AW < transfer_count; count_local_AW++)
      begin
        local_addr = '0;
        local_addr[2+RANDOM_ADDR_BITS-1:2] = $random();
        local_addr = address_base + local_addr;
        ST4_AW ( .id({cmd_id[3:0], count_local_AW[3:0]}), .address(local_addr), .user(SRC_ID) );
      end

      for ( count_local_W = 0; count_local_W < transfer_count; count_local_W++)
      begin
        if($random % 2)
          local_be = { {AXI_NUMBYTES/2{1'b1}},{AXI_NUMBYTES/2{1'b0}} };
        else
          local_be = { {AXI_NUMBYTES/2{1'b0}},{AXI_NUMBYTES/2{1'b1}} };

        local_wdata[0] = $random;
        ST4_DW ( .wdata(local_wdata[0]), .be(local_be), .user(SRC_ID) );
      end
    join
  end


  "8_BYTE" :
  begin
    fork
      for ( count_local_AW = 0; count_local_AW < transfer_count; count_local_AW++)
      begin
        local_addr = '0;
        local_addr[3+RANDOM_ADDR_BITS-1:3] = $random();
        local_addr = address_base + local_addr;
        ST8_AW ( .id({cmd_id[3:0], count_local_AW[3:0]}), .address(local_addr), .user(SRC_ID) );
      end

      for ( count_local_W = 0; count_local_W < transfer_count; count_local_W++)
      begin
        local_wdata[0] = $random;
        ST8_DW ( .wdata(local_wdata[0]), .be('1), .user(SRC_ID) );
      end
    join
  end

  "16_BYTE" :
  begin
    fork
      for ( count_local_AW = 0; count_local_AW < transfer_count; count_local_AW++)
      begin
        local_addr = '0;
        local_addr[4+RANDOM_ADDR_BITS-1:4] = $random();
        local_addr = address_base + local_addr;
        ST8_AW ( .id({cmd_id[3:0], count_local_AW[3:0]}), .address(local_addr),.user(SRC_ID) );
      end

      for ( count_local_W = 0; count_local_W < transfer_count; count_local_W++)
      begin
        local_wdata[0] = $random;
        local_wdata[1] = $random;
        ST8_DW ( .wdata(local_wdata[1:0]), .be('1), .user(SRC_ID) );
      end
    join
  end


  "32_BYTE" :
  begin
    fork
      for ( count_local_AW = 0; count_local_AW < transfer_count; count_local_AW++)
      begin
        local_addr = '0;
        local_addr[5+RANDOM_ADDR_BITS-1:5] = $random();
        local_addr = address_base + local_addr;
        ST16_AW ( .id({cmd_id[3:0], count_local_AW[3:0]}), .address(local_addr), .user(SRC_ID) );
      end

      for ( count_local_W = 0; count_local_W < transfer_count; count_local_W++)
      begin
        local_wdata[0] = $random() ;
        local_wdata[1] = $random() ;
        local_wdata[2] = $random() ;
        local_wdata[3] = $random() ;
        ST16_DW ( .wdata(local_wdata[3:0]), .be('1), .user(SRC_ID) );
      end
    join
  end

  "64_BYTE" :
  begin
    fork
      for ( count_local_AW = 0; count_local_AW < transfer_count; count_local_AW++)
      begin
        local_addr = '0;
        local_addr[6+RANDOM_ADDR_BITS-1:6] = $random();
        local_addr = address_base + local_addr;
        ST4_AW ( .id({cmd_id[3:0], count_local_AW[3:0]}), .address(local_addr), .user(SRC_ID) );
      end

      for ( count_local_W = 0; count_local_W < transfer_count; count_local_W++)
      begin
        local_wdata[0] = $random ;
        local_wdata[1] = $random ;
        local_wdata[2] = $random ;
        local_wdata[3] = $random ;
        local_wdata[4] = $random ;
        local_wdata[5] = $random ;
        local_wdata[6] = $random ;
        local_wdata[7] = $random ;
        ST4_DW ( .wdata(local_wdata[7:0]), .be('1), .user(SRC_ID) );
      end
    join
  end

  default:
    begin
      $error("Unknown transfer type. Please specify the size of the requested transfers.");
    end

  endcase

end
endtask
