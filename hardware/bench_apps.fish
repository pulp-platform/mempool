#!/usr/bin/env fish

for unroll in 1
  for app in axpy dotp convolution dct tests
    echo "Launching $app:"
    set builddir build_$app
    set resultdir results_$app
    mkdir -p $builddir
    mkdir -p $resultdir
    echo "cd $builddir; /scratch/sriedel/projects/mempool/hardware/build/mempool_simvopt +PRELOAD=/scratch/sriedel/projects/mempool/software/bin/$app > transcript; cd -; buildpath=$builddir resultpath=$resultdir make trace >> $builddir/transcript; echo $app done"
    fish -c "cd $builddir; /scratch/sriedel/projects/mempool/hardware/build/mempool_simvopt +PRELOAD=/scratch/sriedel/projects/mempool/software/bin/$app > transcript; cd -; buildpath=$builddir resultpath=$resultdir make trace >> $builddir/transcript; echo $app done" &
  end
  wait
end
