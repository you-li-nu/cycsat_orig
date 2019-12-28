g++ key.cpp -o key -std=c++11

for file in set1/*.bench
do
	file1=$(echo $file | cut -d'.' -f1)
	file2=$(echo $file1 | cut -d'/' -f2)
	file3=$(echo $file2 | cut -d'_' -f1)	

	keyout=$(./key original/$file2.bench set1/$file2.cyc.bench)

	./../../source/src/lcmp	 original/$file3.bench  set1/$file2.cyc.bench $keyout
	
done

for file in set2/*.bench
do
	file1=$(echo $file | cut -d'.' -f1)
	file2=$(echo $file1 | cut -d'/' -f2)
	file3=$(echo $file2 | cut -d'_' -f1)	

	keyout=$(./key iolts14/$file2.bench set2/$file2.cyc.bench)

	./../../source/src/lcmp	 original/$file3.bench  set2/$file2.cyc.bench $keyout
	
done

for file in set3/*.bench
do
	file1=$(echo $file | cut -d'.' -f1)
	file2=$(echo $file1 | cut -d'/' -f2)
	file3=$(echo $file2 | cut -d'_' -f1)	

	keyout=$(./key iolts14/$file2.bench set3/$file2.cyc.bench)

	./../../source/src/lcmp	 revised_original/$file2.orig.bench  set3/$file2.cyc.bench $keyout	
done

