# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).


## Unreleased


## 0.2.0 - 2021-03-29

### Added
- Assertion checking that Snitch's instruction interface is stable during stalls

### Changed
- Update `axi` dependency to 0.27.1
- Change I$ policy to avoid evicting the cache-line currently in use
- Make the L0 cache's data latch-based and double its size
- Make the L1 cache's tag latch-based
- Serialize the L1 lookup

### Fixed
- Add a workaround for a Modelsim 2019 bug in the `axi_demux`
- Keep clang-format from reformatting the `apps/common/riscv_test.h` assembly header file

## 0.1.0 - 2021-03-17
- Initial release.
