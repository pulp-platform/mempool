[![ci](https://github.com/pulp-platform/mempool/actions/workflows/ci.yml/badge.svg)](https://github.com/pulp-platform/mempool/actions/workflows/ci.yml)
[![lint](https://github.com/pulp-platform/mempool/actions/workflows/lint.yml/badge.svg)](https://github.com/pulp-platform/mempool/actions/workflows/lint.yml)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)

# MemPool Family Documentation

## Introduction

MemPool Family is a scalable many-core cluster shared L1 memory system. It mainly includes three configurations: 
- **MinPool**: 16 cores cluster shared 64KiB L1 SPM
- **MemPool**: 256 cores cluster shared 1MiB L1 SPM
- **TeraPool**: 1024 cores cluster shared 4MiB SPM
For more technical details, please refer to our main branch.

## Repository Structure

This repository contains the open-sourced documents for the project. Sharing and distribution are allowed with proper attribution to the original authors and contributors under permissive open source licenses (see [LICENSE](LICENSE)).

### Contents

- **LICENSE**: The license file for the repository.
- **README**: This README file.
- **doc/**: A folder containing the documentation for different workspaces.
  - **mempool_work/**: Documentation specific to MemPool.
  - **terapool_work/**: Documentation specific to TeraPool.

## Publications

## Publications
If you use one/some of MemPool family in your work or research, you can cite us:

**MemPool: A Scalable Manycore Architecture with a Low-Latency Shared L1 Memory**

```
@article{Riedel2023MemPool,
  title = {{MemPool}: A Scalable Manycore Architecture with a Low-Latency Shared {L1} Memory},
  author = {Riedel, Samuel and Cavalcante, Matheus and Andri, Renzo and Benini, Luca},
  journal = {IEEE Transactions on Computers},
  year = {2023},
  volume = {72},
  number = {12},
  pages = {3561--3575},
  publisher = {IEEE Computer Society},
  doi = {10.1109/TC.2023.3307796}
}
```
This paper was published on [IEEE Xplore](https://ieeexplore.ieee.org/document/10227739) and is also available on [arXiv:2303.17742 [cs.AR]](https://arxiv.org/abs/2303.17742) and the [ETH Research Collection](https://doi.org/10.3929/ethz-b-000643341).


The following publications give more details about MemPool, its extensions, and use cases:

### 2021

<details>
<summary><i>MemPool: A Shared-L1 Memory Many-Core Cluster with a Low-Latency Interconnect</i></summary>
<p>

```
@inproceedings{Cavalcante2021MemPool,
  title = {{MemPool}: A Shared-{L1} Memory Many-Core Cluster with a Low-Latency Interconnect},
  author = {Cavalcante, Matheus and Riedel, Samuel and Pullini, Antonio and Benini, Luca},
  booktitle = {2021 Design, Automation, and Test in Europe Conference and Exhibition},
  address = {Grenoble, France},
  year = {2021},
  month = mar,
  pages = {701--706},
  publisher = {IEEE},
  doi = {10.23919/DATE51398.2021.9474087}
}
```
This paper was published on [IEEE Xplore](https://ieeexplore.ieee.org/document/9474087) and is also available on [arXiv:2012.02973 [cs.AR]](https://arxiv.org/abs/2012.02973).

</p>
</details>


<details>
<summary><i>3D SoC integration, beyond 2.5D chiplets</i></summary>
<p>

```
@inproceedings{Beyne2021,
  title = {{3D} {SoC} integration, beyond {2.5D} chiplets},
  author = {Beyne, Eric and Milojevic, Dragomir and {Van Der Plas}, Geert and Beyer, Gerald},
  booktitle = {Technical Digest - International Electron Devices Meeting, IEDM},
  year = {2021},
  pages = {79--82},
  publisher = {IEEE},
  doi = {10.1109/IEDM19574.2021.9720614}
}
```
This paper was published on [IEEE Xplore](https://ieeexplore.ieee.org/document/9720614).

</p>
</details>


### 2022

<details>
<summary><i>MemPool-3D: Boosting Performance and Efficiency of Shared-L1 Memory Many-Core Clusters with 3D Integration</i></summary>
<p>

```
@inproceedings{Cavalcante2022MemPool3D,
  title = {{MemPool-3D}: Boosting Performance and Efficiency of Shared-{L1} Memory Many-Core Clusters with {3D} Integration},
  author = {Cavalcante, Matheus and Agnesina, Anthony and Riedel, Samuel and Brunion, Moritz and Garcia-Ortiz, Alberto and Milojevic, Dragomir and Catthoor, Francky and Lim, Sung Kyu and Benini, Luca},
  booktitle = {2022 Design, Automation, and Test in Europe Conference and Exhibition},
  address = {Online},
  year = {2022},
  month = mar,
  pages = {394--399},
  publisher = {IEEE},
  doi = {10.23919/DATE54114.2022.9774726}
}
```
This paper was published on [IEEE Xplore](https://ieeexplore.ieee.org/document/9774726) and is also available on [arXiv:2112.01168 [cs.AR]](https://arxiv.org/abs/2112.01168).

</p>
</details>


<details>
<summary><i>Hier-3D: A Hierarchical Physical Design Methodology for Face-to-Face-Bonded 3D ICs</i></summary>
<p>

```
@inproceedings{Agnesina2022,
  title = {{Hier-3D}: A Hierarchical Physical Design Methodology for Face-to-Face-Bonded {3D} ICs},
  author = {Agnesina, Anthony and Brunion, Moritz and Garcia-Ortiz, Alberto and Catthoor, Francky and Milojevic, Dragomir and Komalan, Manu and Cavalcante, Matheus and Riedel, Samuel and Benini, Luca and Lim, Sung Kyu},
  booktitle = {Proceedings of the ACM/IEEE International Symposium on Low Power Electronics and Design},
  address = {New York, NY, USA},
  year = {2022},
  month = aug,
  publisher = {Association for Computing Machinery},
  doi = {10.1145/3531437.3539702}
}
```
This paper was published on [ACM DL](https://dl.acm.org/doi/10.1145/3531437.3539702).


</p>
</details>


<details>
<summary><i>Spatz: A Compact Vector Processing Unit for High-Performance and Energy-Efficient Shared-L1 Clusters</i></summary>
<p>

```
@inproceedings{Cavalcante2022Spatz,
  title = {Spatz: A Compact Vector Processing Unit for High-Performance and Energy-Efficient Shared-{L1} Clusters},
  author = {Cavalcante, Matheus and W{\"{u}}thrich, Domenic and Perotti, Matteo and Riedel, Samuel and Benini, Luca},
  booktitle = {2022 IEEE/ACM International Conference On Computer Aided Design (ICCAD)},
  address = {San Diego, California, USA},
  year = {2022},
  month = oct,
  pages = {159--167},
  publisher = {Association for Computing Machinery},
  doi = {10.1145/3508352.3549367}
}
```
This paper was published on [IEEE Xplore](https://ieeexplore.ieee.org/document/10069431) and is also available on [arXiv:2207.07970 [cs.AR]](https://arxiv.org/abs/2207.07970).

</p>
</details>


<details>
<summary><i>Thermal Performance Analysis of Mempool RISC-V Multicore SoC</i></summary>
<p>

```
@article{Venkateswarlu2022,
  title = {Thermal Performance Analysis of Mempool RISC-V Multicore {SoC}},
  author = {Venkateswarlu, Sankatali and Mishra, Subrat and Oprins, Herman and Vermeersch, Bjorn and Brunion, Moritz and Han, Jun Han and Stan, Mircea R. and Weckx, Pieter and Catthoor, Francky},
  journal = {IEEE Transactions on Very Large Scale Integration (VLSI) Systems},
  year = {2022},
  volume = {30},
  number = {11},
  pages = {1668--1676},
  publisher = {IEEE},
  doi = {10.1109/TVLSI.2022.3207553}
}
```
This paper was published on [IEEE Xplore](https://ieeexplore.ieee.org/document/9905665).

</p>
</details>


### 2023

<details>
<summary><i>Towards Chip-Package-System Co-optimization of Thermally-limited System-On-Chips (SOCs)</i></summary>
<p>

```
@inproceedings{Mishra2023,
  title = {Towards Chip-Package-System Co-optimization of Thermally-limited System-On-Chips (SOCs)},
  author = {Mishra, S. and Sankatali, V. and Vermeersch, B. and Brunion, M. and Lofrano, M. and Abdi, D. and Oprins, H. and Biswas, D. and Zografos, O. and Hiblot, G. and {Van Der Plas}, G. and Weckx, P. and Hellings, G. and Myers, J. and Catthoor, F. and Ryckaert, J.},
  booktitle = {IEEE International Reliability Physics Symposium Proceedings},
  address = {Monterey, CA, USA},
  year = {2023},
  month = mar,
  publisher = {IEEE},
  doi = {10.1109/IRPS48203.2023.10117979}
}
```
This paper was published on [IEEE Xplore](https://ieeexplore.ieee.org/document/10117979).

</p>
</details>


<details>
<summary><i>Efficient Parallelization of 5G-PUSCH on a Scalable RISC-V Many-Core Processor</i></summary>
<p>

```
@inproceedings{Bertuletti2023PUSCH,
  title = {Efficient Parallelization of {5G-PUSCH} on a Scalable {RISC-V} Many-Core Processor},
  author = {Bertuletti, Marco and Zhang, Yichao and Vanelli-Coralli, Alessandro and Benini, Luca},
  booktitle = {2023 Design, Automation, and Test in Europe Conference and Exhibition},
  address = {Antwerp, Belgium},
  year = {2023},
  month = apr,
  pages = {396--401},
  publisher = {IEEE},
  doi = {10.23919/DATE56975.2023.10137247}
}
```
This paper was published on [IEEE Xplore](https://ieeexplore.ieee.org/document/10137247) and is also available on [arXiv:2210.09196 [cs.DC]](https://arxiv.org/abs/2210.09196).

</p>
</details>


<details>
<summary><i>MemPool Meets Systolic: Flexible Systolic Computation in a Large Shared-Memory Processor Cluster</i></summary>
<p>

```
@inproceedings{Riedel2023MmS,
  title = {{MemPool} Meets Systolic: Flexible Systolic Computation in a Large Shared-Memory Processor Cluster},
  author = {Riedel, Samuel and Khov, Gua Hao and Mazzola, Sergio and Cavalcante, Matheus and Andri, Renzo and Benini, Luca},
  booktitle = {2023 Design, Automation, and Test in Europe Conference and Exhibition},
  address = {Antwerp, Belgium},
  year = {2023},
  month = apr,
  pages = {503--504},
  publisher = {IEEE},
  doi = {10.23919/DATE56975.2023.10136909}
}
```
This paper was published on [IEEE Xplore](https://ieeexplore.ieee.org/document/10136909).

</p>
</details>


<details>
<summary><i>Fast Shared-Memory Barrier Synchronization for a 1024-Cores RISC-V Many-Core Cluster</i></summary>
<p>

```
@inproceedings{Bertuletti2023Barrier,
  title = {Fast Shared-Memory Barrier Synchronization for a 1024-Cores {RISC-V} Many-Core Cluster},
  author = {Bertuletti, Marco and Riedel, Samuel and Zhang, Yichao and Vanelli-Coralli, Alessandro and Benini, Luca},
  booktitle = {Embedded Computer Systems: Architectures, Modeling, and Simulation},
  editor = {Silvano, Cristina and Pilato, Christian and Reichenbach, Marc},
  address = {Samos},
  year = {2023},
  month = jul,
  pages = {241--254},
  publisher = {Springer Nature Switzerland},
  doi = {10.1007/978-3-031-46077-7_16}
}
```
This paper was published on [Springer Link](https://link.springer.com/chapter/10.1007/978-3-031-46077-7_16) and is also available on [arXiv:2307.10248 [cs.DC]](https://arxiv.org/abs/2307.10248) and the [ETH Research Collection](https://doi.org/10.3929/ethz-b-000648454).

</p>
</details>


<details>
<summary><i>MemPool: A Scalable Manycore Architecture with a Low-Latency Shared L1 Memory</i></summary>
<p>

```
@article{Riedel2023MemPool,
  title = {{MemPool}: A Scalable Manycore Architecture with a Low-Latency Shared {L1} Memory},
  author = {Riedel, Samuel and Cavalcante, Matheus and Andri, Renzo and Benini, Luca},
  journal = {IEEE Transactions on Computers},
  year = {2023},
  volume = {72},
  number = {12},
  pages = {3561--3575},
  publisher = {IEEE Computer Society},
  doi = {10.1109/TC.2023.3307796}
}
```
This paper was published on [IEEE Xplore](https://ieeexplore.ieee.org/document/10227739) and is also available on [arXiv:2303.17742 [cs.AR]](https://arxiv.org/abs/2303.17742) and the [ETH Research Collection](https://doi.org/10.3929/ethz-b-000643341).

</p>
</details>


<details>
<summary><i>Impact of 3-D Integration on Thermal Performance of RISC-V MemPool Multicore SOC</i></summary>
<p>

```
@article{Venkateswarlu2023,
  title = {Impact of 3-D Integration on Thermal Performance of {RISC-V} {MemPool} Multicore {SOC}},
  author = {Venkateswarlu, Sankatali and Mishra, Subrat and Oprins, Herman and Vermeersch, Bjorn and Brunion, Moritz and Han, Jun Han and Stan, Mircea R. and Biswas, Dwaipayan and Weckx, Pieter and Catthoor, Francky},
  journal = {IEEE Transactions on Very Large Scale Integration (VLSI) Systems},
  year = {2023},
  volume = {31},
  number = {12},
  pages = {1896-1904},
  publisher = {IEEE},
  doi = {10.1109/TVLSI.2023.3314135}
}
```
This paper was published on [IEEE Xplore](https://ieeexplore.ieee.org/document/10261872).

</p>
</details>


<details>
<summary><i>MinPool: A 16-core NUMA-L1 Memory RISC-V Processor Cluster for Always-on Image Processing in 65nm CMOS</i></summary>
<p>

```
@inproceedings{Riedel2023MinPool,
  author={Riedel, Samuel and Cavalcante, Matheus and Frouzakis, Manos and Wüthrich, Domenic and Mustafa, Enis and Billa, Arlind and Benini, Luca},
  title={{MinPool}: A 16-core {NUMA-L1} Memory {RISC-V} Processor Cluster for Always-on Image Processing in 65nm {CMOS}},
  booktitle={2023 30th IEEE International Conference on Electronics, Circuits and Systems (ICECS)},
  address = {Istanbul, Turkiye},
  year={2023},
  month=dec,
  pages={1--4},
  publisher={IEEE},
  doi={10.1109/ICECS58634.2023.10382925}
}
```
This paper was published on [IEEE Xplore](https://ieeexplore.ieee.org/document/10382925) and is also available on the [ETH Research Collection](https://doi.org/10.3929/ethz-b-000653598).

</p>
</details>

### 2024

<details>
<summary><i>LRSCwait: Enabling Scalable and Efficient Synchronization in Manycore Systems through Polling-Free and Retry-Free Operation</i></summary>
<p>

```
@article{Riedel2024LRSCwait,
      title={{LRSCwait}: Enabling Scalable and Efficient Synchronization in Manycore Systems through Polling-Free and Retry-Free Operation},
      author={Samuel Riedel and Marc Gantenbein and Alessandro Ottaviano and Torsten Hoefler and Luca Benini},
      journal={arXiv:2401.09359 [cs.AR]},
      year={2024},
      month=jan
}
```
This paper is available on [arXiv:2401.09359 [cs.AR]](https://arxiv.org/abs/2401.09359).

</p>
</details>


<details>
<summary><i>Enabling Efficient Hybrid Systolic Computation in Shared L1-Memory Manycore Clusters</i></summary>
<p>

```
@article{Mazzola2024Systolic,
      title={Enabling Efficient Hybrid Systolic Computation in Shared {L1}-Memory Manycore Clusters},
      author={Sergio Mazzola and Samuel Riedel and Luca Benini},
      journal={arXiv:2402.12986 [cs.AR]},
      year={2024},
      month=feb
}
```
This paper is available on [arXiv:2402.12986 [cs.AR]](https://arxiv.org/abs/2402.12986).

</p>
</details>

<details>
<summary><i>TeraPool-SDR: An 1.89TOPS 1024 RV-Cores 4MiB Shared-L1 Cluster for Next-Generation Open-Source Software-Defined Radios</i></summary>
<p>

```
@artical{perotti2024mx,
      title={MX: Enhancing RISC-V's Vector ISA for Ultra-Low Overhead, Energy-Efficient Matrix Multiplication}, 
      author={Matteo Perotti and Yichao Zhang and Matheus Cavalcante and Enis Mustafa and Luca Benini},
      year={2024},
      month=feb
}
```
This paper is available on [arXiv:2401.04012 [cs.AR]](https://arxiv.org/abs/2401.04012).

</p>
</details>

<details>
<summary><i>TeraPool-SDR: An 1.89TOPS 1024 RV-Cores 4MiB Shared-L1 Cluster for Next-Generation Open-Source Software-Defined Radios</i></summary>
<p>

```
@article{Yichao2024Terapool,
      title={TeraPool-SDR: An 1.89TOPS 1024 RV-Cores 4MiB Shared-L1 Cluster for Next-Generation Open-Source Software-Defined Radios},
      author={Yichao Zhang and Marco Bertuletti and Samuel Riedel and Matheus Cavalcante and Alessandro Vanelli-Coralli and Luca Benini},
      journal={arXiv:2405.04988 [cs.DC]},
      year={2024},
      month=may
}
```
This paper is available on [arXiv:2405.04988 [cs.DC]](https://arxiv.org/abs/2405.04988).

</p>
</details>


## Chips

The MemPool architecture has been taped out in the following chips:

- 2021 [**MinPool**](http://asic.ethz.ch/2021/Minpool.html): A 16-core prototype of MemPool.
- 2024 [**Heartstream**](http://asic.ethz.ch/2024/Heartstream.html): A 64-core version of MemPool with systolic and FPU support.

## License

All sources are released under Apache Version 2.0. See the [LICENSE](LICENSE) file for more information.
