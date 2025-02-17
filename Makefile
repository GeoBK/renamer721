CC = g++
#OPT = -O3
OPT = -g

INC = -I.
LIB = -L.

CFLAGS = $(OPT) $(INC) $(LIB)

SRC = renamer.cc glue.cc
OBJ = renamer.o glue.o
LIBS = -l721sim -lriscv-base -lpthread -lz -ldl 


#################################

all: $(OBJ)
	$(CC) $(CFLAGS) -o 721sim $(OBJ) $(LIBS)
	@echo "-----------DONE WITH 721sim-----------"
 
.cc.o:
	$(CC) $(CFLAGS) -c $*.cc



clean:
	rm -f *.o 721sim core
clobber:
	rm -f *.o
