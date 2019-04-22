from z3 import *
import arr_test as ar
g = Goal()

main_var_0_0 = BitVec('main_var_0_0', 32)
g.add(And(ar.gte(main_var_0_0, 0), ar.lte(main_var_0_0, 99)))
main_var_2_0 = BitVec('main_var_2_0', 32)
g.add(main_var_2_0 == main_var_0_0)
main_var_3_0 = Bool('main_var_3_0')
g.add(main_var_3_0 == (main_var_2_0 < 5))
g.add(main_var_3_0 == False)
main_var_8_0 = BitVec('main_var_8_0', 32)
g.add(main_var_8_0 == 3)
main_var_9_0 = Bool('main_var_9_0')
g.add(main_var_9_0 == (main_var_8_0 == 4))
g.add(main_var_9_0 == False)
main_var_11_0 = BitVec('main_var_11_0', 32)
g.add(main_var_11_0 == main_var_8_0)

t = Then('simplify', 'bit-blast', 'tseitin-cnf')
subgoal = t(g)
assert len(subgoal) == 1
print subgoal[0].sexpr()
