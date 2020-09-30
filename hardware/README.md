# Traffic Generator

Run multiple parallel simulations with:
``` bash
# Create a test_sequence file with the interesting req_probabilities
cat test_sequence | parallel -j 4 make simc buildpath=build_{}_1000 req_prob={} seq_prob=1000
# Run all cases from 10 - 1000
seq 10 10 1000 | parallel -j 4 make simc buildpath=build_{}_1000 req_prob={} seq_prob=1000
```

Copy the files and parse them:
``` bash
rsync -av "<path>/mempool/hardware/build_*" results --exclude "*work*" --exclude "*modelsim*" --exclude "*.tcl"
for d in results_*/ ; do
  echo $d
  python3.6 ../scripts/parse_tg.py $d
done
```
