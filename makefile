all: compile clean

compile:
	coqc ListSets.v
	coqc NFA.v
	coqc DFA.v
	coqc Reversing.v
	coqc Normalization.v
	coqc Pumping.v
	coqc Determinization.v
	coqc Brzozowski.v
	coqc Brzozowski_complete.v

clean:
	@rm -f .*.aux *.glob *.vok *.vos