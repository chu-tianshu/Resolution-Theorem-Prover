# Resolution-Theorem-Prover
This programs reads in clause sets from txt files, parses them and derives conclusions from them by use of the resolution algorithm.

1. Input format
Each line of the format in the input file denotes a clause. A clause should be in the format as follows:
(positive literals) (negative literals)
A literal should be in the format as follows:
(funcName argument1 argument2)
Basically a literal is denoted by a string with parentheses on its two ends, and the substring in between is a list of strings splitted by spaces, and the first word in it is the function name, and all the other words are each arguments.

2. How to run
Each time you will need to set up the following variables in order to run the prover:
(1) FILE_PATH: where the input file is located
(2) GOAL_CLAUSE_START_INDEX: the index from which all the clauses following are negated conclusions
(3)	IS_UNIT_PREFERENCE: false -> two pointer; true -> unit preference
