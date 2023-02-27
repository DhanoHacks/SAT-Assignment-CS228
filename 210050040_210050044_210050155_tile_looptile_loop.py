### TEAM MEMBERS
## MEMBER 1: 210050040
## MEMBER 2: 210050044
## MEMBER 3: 210050155


from z3 import *
import sys, re
file = sys.argv[1]

def generate_move_clause(t, move, bool_row, bool_inc):
    move_clause = []
    binary_move = f"{move:b}"+bool_row+bool_inc
    binary_move = "0"*(len(f"{n-1:b}")+2-len(binary_move))+binary_move
    for bit in range(len(binary_move)):
        if binary_move[-bit-1] == "0":
            move_clause.append(Not(all_moves[t][bit]))
        else:
            move_clause.append(all_moves[t][bit])
    return And(move_clause)

def generate_pos_clause(t, binary_position, num):
    pos_clause = []
    for bit in range(len(binary_position)):
        if binary_position[-bit-1] == "0":
            pos_clause.append(Not(all_states[t][num][bit]))
        else:
            pos_clause.append(all_states[t][num][bit])
    return And(pos_clause)

with open(file) as f:
	n,T = [int(x) for x in next(f).split()]
	matrix = []
	for line in f:
		matrix.append([int(x) for x in line.split()])

s = Solver()
all_states = []
all_moves = []

# variables defining state of the board
for t in range(T+1):
    one_state=[]
    for i in range(n*n):
        one_number=[]
        for j in range(len(f"{n*n-1:b}")):
            one_number.append(Bool(f"board_{t}_num_{i}_bit_{j}"))
        one_state.append(one_number)
    all_states.append(one_state)

# variables defining the move done at every step
for t in range(T):
    one_move = []
    one_move.append(Bool(f"move_{t}_inc_or_dec"))
    one_move.append(Bool(f"move_{t}_row_or_col"))
    for j in range(len(f"{n-1:b}")):
        one_move.append(Bool(f"move_{t}_position_bit_{j}"))
    all_moves.append(one_move)

# clauses for initializing the board
t = 0
for i in range(n):
    for j in range(n):
        idx_binary = f"{i*n+j:b}"
        idx_binary = "0"*(len(f"{n*n-1:b}")-len(idx_binary))+idx_binary
        for bit in range(len(idx_binary)):
            if idx_binary[-bit-1] == "0":
                s.add(Not(all_states[t][matrix[i][j]-1][bit]))
            else:
                s.add(all_states[t][matrix[i][j]-1][bit])

# clauses for maintaining valid state of board
# for t in range(T+1):
#     for i1 in range(n*n):
#         for i2 in range(n*n):
#             if i1 != i2:
#                 or_clause = []
#                 for j in range(len(f"{n*n-1:b}")):
#                     or_clause.append(Xor(all_states[t][i1][j],all_states[t][i2][j]))
#                 s.add(Or(or_clause))

# clauses for changing state of board by applying a move
for t in range(T):
    # move_clauses = []
    for (bool_inc,bool_row) in [("0","0"),("0","1"),("1","0"),("1","1")]:
        for move in range(n):
            move_clause = generate_move_clause(t, move, bool_row, bool_inc)
            is_inc = 1 if bool_inc == "1" else -1 # "1" - increment, "0" - decrement
            is_row = bool_row == "1" # "1" - row shift, "0" - column shift
            shift_clause = []
            
            i = move
            for j in range(n):
                for num in range(n*n):
                    if is_row:
                        binary_current_position = f"{i*n+j:b}"
                        binary_next_position = f"{i*n+(j+is_inc)%n:b}"
                    else:
                        binary_current_position = f"{j*n+i:b}"
                        binary_next_position = f"{((j+is_inc)%n)*n+i:b}"

                    binary_current_position = "0"*(len(f"{n*n-1:b}")-len(binary_current_position))+binary_current_position
                    binary_next_position = "0"*(len(f"{n*n-1:b}")-len(binary_next_position))+binary_next_position

                    current_pos_clause = generate_pos_clause(t, binary_current_position, num)
                    next_pos_clause = generate_pos_clause(t+1, binary_next_position, num)
                    shift_clause.append(Implies(current_pos_clause,next_pos_clause))

            shift_clause = And(shift_clause)
            # move_clauses.append(Implies(move_clause,shift_clause))
            s.add(Implies(move_clause,shift_clause))
    # s.add(And(move_clauses))


    for num in range(n*n):
        for pos in range(n*n):
            i = pos//n
            j = pos%n
            binary_position = f"{pos:b}"
            binary_position = "0"*(len(f"{n*n-1:b}")-len(binary_position))+binary_position
            current_pos_clause = generate_pos_clause(t, binary_position, num)
            next_pos_same = generate_pos_clause(t+1, binary_position, num)

            other_positions = [f"{i*n+(j+1)%n:b}",f"{i*n+(j-1)%n:b}",f"{((i+1)%n)*n+j:b}",f"{((i-1)%n)*n+j:b}"]
            other_positions = ["0"*(len(f"{n*n-1:b}")-len(bpos))+bpos for bpos in other_positions]
            other_pos_clauses = [generate_pos_clause(t+1, bpos, num) for bpos in other_positions]
            corresponding_move_clauses = [generate_move_clause(t,i,"1","1"),generate_move_clause(t,i,"1","0"),generate_move_clause(t,j,"0","1"),generate_move_clause(t,j,"0","0")]

            s.add(Implies(current_pos_clause,Or([next_pos_same]+[And(other_pos_clauses[i],corresponding_move_clauses[i]) for i in range(4)])))

# clauses for win condition of game
or_clause = []
t = T
one_state_win = []
for required_num_at_idx in range(n*n):
    idx_binary = f"{required_num_at_idx:b}"
    idx_binary = "0"*(len(f"{n*n-1:b}")-len(idx_binary))+idx_binary
    for bit in range(len(idx_binary)):
        if idx_binary[-bit-1] == "0":
            one_state_win.append(Not(all_states[t][required_num_at_idx][bit]))
        else:
            one_state_win.append(all_states[t][required_num_at_idx][bit])
or_clause.append(And(one_state_win))
s.add(Or(or_clause))

# Output the moves
x = s.check()
print(x)
if x == sat:
    m = s.model()
    # model = sorted ([(d, m[d]) for d in m], key = lambda x: str(x[0]))
    # for line in model:
    #     print(line)
    moves = [{} for i in range(T)]
    for d in m.decls():
        if "move" in d.name():
            # print(d.name())
            i = int(re.findall("move_[0-9]+",d.name())[0].strip("move_"))
            moves[i][d.name()]=(1 if m[d] else 0)
    for i in range(len(moves)):
        type_of_move = [["u","d"],["l","r"]][moves[i][f"move_{i}_row_or_col"]][moves[i][f"move_{i}_inc_or_dec"]]
        position_of_move = ""
        for j in range(len(f"{n-1:b}")):
            position_of_move = str(moves[i][f"move_{i}_position_bit_{j}"]) + position_of_move
        position_of_move = eval("0b"+position_of_move)
        if position_of_move<n:
            print(f"{position_of_move}{type_of_move}")