
#####################################################################################################
COURSE=CMPS 112
ASGN=hw0
COMPILER=ghuang6
#####################################################################################################

test:
	stack test

bin:
	stack build

clean:
	stack clean

prepare: clean
	tar -zcvf ../$(ASGN)-$(COMPILER).tgz --exclude .git --exclude .stack-work ../$(ASGN)-$(COMPILER)
	mv ../$(ASGN)-$(COMPILER).tgz .
