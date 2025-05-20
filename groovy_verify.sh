#! /bin/bash 
FUEL=${1:-4}
SIZE=${2:-100}

# clean
rm -f *.info
rm -f *.class

# gen code samples
./build/exec/dynam -n $SIZE --model-fuel=$FUEL groovy


for (( i = 0; i < $SIZE; ++i )); do
    echo "Compile #$i"

    if ! groovyc tests$i.info; then
        cat tests$i.info
        exit 43
    fi
done


echo "== DONE =="
cat coverage.info
