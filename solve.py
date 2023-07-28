import z3
import sys
from dataclasses import dataclass
import random

# formats for the constraint table:
# (opcode, s, t, [(i, v)])
@dataclass
class Constraint:
    opcode : str
    s : int
    t : int
    is_binary : bool
    assignments : ...

def parse(f):
    num_insts = int(next(f))
    constraints = []
    for _ in range(num_insts):
        # example: _mm_broadcastw_epi16 0 128 0 16
        opcode, ty, bitwidth, _, num_constraints = next(f).strip().split()
        for _ in range(int(num_constraints)):
            s, t, num_bits = next(f).strip().split()
            assignments = []
            for _ in range(int(num_bits)):
                i, v = map(int, next(f).strip().split())
                assignments.append((i, v))
            constraints.append(Constraint(opcode=opcode, s=int(s), t=int(t), is_binary=int(ty)>=3, assignments=assignments))
    return constraints

with open(sys.argv[1]) as f:
    constraints = parse(f)

'''
sketch of the program:
out1 = op1 x, y
out2 = op2 out1
out3 = op3 out3
'''
def make_bytes(prefix):
    return [z3.BitVec('%s%d'%(prefix,i), 8) for i in range(16)]
def make_bits(prefix):
    return [z3.Bool('%s%d'%(prefix,i)) for i in range(128)]

######## smt vars ####
var_x = make_bytes('x')
var_y = make_bytes('y')
var_out1 = make_bytes('out1')
var_out2 = make_bytes('out2')
var_out3 = make_bytes('out3')
op1 = z3.BitVec('op1', 7)
op2 = z3.BitVec('op2', 7)
op3 = z3.BitVec('op3', 7)
control1 = make_bits('control1')
control2 = make_bits('control2')
control3 = make_bits('control3')
######################

x_val = random.randint(0, (1<<128)-1)
y_val = random.randint(0, (1<<128)-1)
def get_byte(x, i):
    # return the i'th byte of x
    return (x >> (i * 8)) & 0xff

def assert_equal(solver, a : list, b, num_bytes=16):
    for i in range(num_bytes):
        solver.add(a[i] == get_byte(b, i))

opcode_to_number = {}
number_to_opcode = {}
unary_opcodes = set()
binary_opcodes = set()

def is_binary(opcode):
    return opcode in binary_opcodes

def is_unary(opcode):
    return opcode in unary_opcodes

def assign_opcode_number(c : Constraint):
    opcode = c.opcode
    if c.is_binary:
        binary_opcodes.add(opcode)
    else:
        unary_opcodes.add(opcode)
    if opcode in opcode_to_number:
        return
    num = len(opcode_to_number)
    opcode_to_number[opcode] = num
    number_to_opcode[num] = opcode

def select_byte(x, y, i):
    if i < 16:
        return x[i]
    return y[i - 16]

for c in constraints:
    assign_opcode_number(c)

solver = z3.Solver()
assert_equal(solver, var_x, x_val)
assert_equal(solver, var_y, y_val)

out = var_out3
bytes = [i for i in range(32) if i % 2 == 1]
bytes.reverse()
#bytes = [0] * 16
for i, j in enumerate(bytes):
    solver.add(out[i] == select_byte(var_x, var_y, j))

# encode the first instruction
for c in constraints:
    if not c.is_binary:
        continue
    matches = [op1 == opcode_to_number[c.opcode]]
    for i, v in c.assignments:
        bit = control1[i]
        matches.append(bit if v==1 else z3.Not(bit))
    input_byte = select_byte(var_x, var_y, c.s)
    output_byte = var_out1[c.t]
    solver.add(z3.Implies(z3.And(matches), input_byte==output_byte))

foo = []
# encode the second instruction (unary)
for c in constraints:
    if c.is_binary:
        continue
    matches = [op2 == opcode_to_number[c.opcode]]
    for i, v in c.assignments:
        bit = control2[i]
        matches.append(bit if v==1 else z3.Not(bit))
    input_byte = var_out1[c.s]
    output_byte = var_out2[c.t]
    solver.add(z3.Implies(z3.And(matches), input_byte==output_byte))
    foo.append(z3.Implies(z3.And(matches), input_byte==output_byte))
print(foo)
exit()

# encode the second instruction (unary)
for c in constraints:
    if c.is_binary:
        continue
    matches = [op3 == opcode_to_number[c.opcode]]
    for i, v in c.assignments:
        bit = control2[i]
        matches.append(bit if v==1 else z3.Not(bit))
    input_byte = var_out2[c.s]
    output_byte = var_out3[c.t]
    solver.add(z3.Implies(z3.And(matches), input_byte==output_byte))

solver.add(z3.Or([op1 == num
    for opcode, num in opcode_to_number.items() if is_binary(opcode)]))
solver.add(z3.Or([op2 == num
    for opcode, num in opcode_to_number.items() if is_unary(opcode)]))
solver.add(z3.Or([op3 == num
    for opcode, num in opcode_to_number.items() if is_unary(opcode)]))

print(solver)
exit()

def as_int(x):
    return x.as_long()

solver.check()
m = solver.model()
#print(m)
print('op1 =', number_to_opcode[as_int(m.eval(op1))])
print('op2 =', number_to_opcode[as_int(m.eval(op2))])
print('op3 =', number_to_opcode[as_int(m.eval(op3))])
