## CycSAT-I original version


### CycSAT: SAT-based attack on cyclic logic encryptions
### [Northwestern University](http://users.eecs.northwestern.edu/~haizhou/)

### Installation:

* dependencies:

 It should work on Ubuntu 14.04-18.04 or other Linux distributions, GCC 5-7 (gcc-5 and g++-5 are recommended), CPLEX12.5-12.9. Sometimes you may need to slightly adjust build options in makefile in source/src/.

 Our work uses the framework in [this repository](https://bitbucket.org/spramod/host15-logic-encryption/src/default/) by Princeton University.

* install dependencies:

```Bash
sudo apt-get install gcc-5  
sudo apt-get install g++-5  
```

```Bash
sudo apt-get install flex-old bison
sudo apr-get install flex  
sudo apt-get install libboost-all-dev
```

* build cudd-2.5.0

```Bash
cd source/cudd-2.5.0/  
make clean  
make  
cd obj    
make clean  
make  
cd ../../..
```

* build minisat

```Bash
cd source/minisat  
export MROOT=$PWD  
cd core  
make libr  
cd ../../..
```

* build CryptoMinisat

```Bash
cd source/cmsat-2.9.9/  
mkdir build  
cd build  
../configure    
make clean  
make  
cd ../../..
```

* build lingeling

```Bash
cd source/lingeling/ 
make clean   
./configure.sh  
make  
cd ../..
```

* clean repository

```Bash
cd source/src/  
make clean
```

* install CPLEX

obtain from [IBM official website](https://developer.ibm.com/docloud/documentation/optimization-modeling/cplex-studio-ce/)

or obtain from [Baidu Disk](https://pan.baidu.com/s/1ONiOS_hS9mFBk7AJ6kTjgw)

after installation,

```Bash
cd source/src/
```

modify makefile entries to include your CPLEX paths:

```Bash
$ CPLEXINCLUDE:  
$ CPLEXLIBRARIES:
```

* build project

```Bash
make
```

* run a test case

```Bash
./sld ../../benchmarks/cyclic_benchmarks/set1/apex2.cyc.bench ../../benchmarks/original/apex2.bench
```


### Cite this repository:

@inproceedings{rezaei2019cycsat,  
  title={CycSAT-unresolvable cyclic logic encryption using unreachable states},  
  author={Rezaei, Amin and Li, You and Shen, Yuanqi and Kong, Shuyu and Zhou, Hai},  
  booktitle={Proceedings of the 24th Asia and South Pacific Design Automation Conference},  
  pages={358--363},  
  year={2019},  
  organization={ACM}  
}

@inproceedings{shen2019besat,  
  title={BeSAT: behavioral SAT-based attack on cyclic logic encryption},  
  author={Shen, Yuanqi and Li, You and Rezaei, Amin and Kong, Shuyu and Dlott, David and Zhou, Hai},  
  booktitle={Proceedings of the 24th Asia and South Pacific Design Automation Conference},  
  pages={657--662},  
  year={2019},  
  organization={ACM}  
}