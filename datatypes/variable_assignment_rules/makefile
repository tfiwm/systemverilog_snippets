all: comp sim

comp: 
	vlog test.sv
sim:
	vsim -c test -do "run -a; q "
clean:
	rm -rf velocework transcript
