root_dir=$(git rev-parse --show-toplevel)
cd $root_dir/software/tests/baremetal;
config=terapool make memcpy;
cd $root_dir/hardware;
app=tests/baremetal/memcpy config=terapool make sim;
cd -;
