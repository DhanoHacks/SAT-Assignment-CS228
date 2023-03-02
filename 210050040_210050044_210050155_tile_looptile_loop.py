### TEAM MEMBERS
## MEMBER 1: 210050040
## MEMBER 2: 210050044
## MEMBER 3: 210050155


from z3 import *
import sys, re
file = sys.argv[1]

# generate clause representing row/column "move" is incremented/decremented by one
def generate_move_clause(t, move, bool_row, bool_inc):
    move_clause = []
    last_two_bits = bool_row+bool_inc
    for bit in range(len(last_two_bits)):
        if last_two_bits[-bit-1] == "0":
            move_clause.append(Not(all_moves[t][bit]))
        else:
            move_clause.append(all_moves[t][bit])
    move_clause.append(all_moves[t][2]==move)
    return And(move_clause)

with open(file) as f:
	n,T = [int(x) for x in next(f).split()]
	matrix = []
	for line in f:
		matrix.append([int(x) for x in line.split()])

# variables defining state of the board
all_states = []
for t in range(T+1):
    one_state=[]
    for i in range(n*n):
        one_number = Int(f"board_{t}_num_{i}_pos")
        one_state.append(one_number)
    all_states.append(one_state)

# variables defining the move done at every step
all_moves = []
for t in range(T):
    one_move = []
    one_move.append(Bool(f"move_{t}_inc_or_dec"))
    one_move.append(Bool(f"move_{t}_row_or_col"))
    one_move.append(Int(f"move_{t}_pos"))
    all_moves.append(one_move)

# initializing solver
s = Solver()

# clauses for initializing the board
t = 0
for i in range(n):
    for j in range(n):
        s.add(all_states[t][matrix[i][j]-1]==i*n+j)

# clause for win condition of game
t = T
win_state = []
for required_num_at_idx in range(n*n):
    s.add(all_states[t][required_num_at_idx]==required_num_at_idx)
s.add(And(win_state))

# clauses for changing state of board by applying a move
for t in range(T):
    for num in range(n*n):
        for pos in range(n*n):
            i = pos//n
            j = pos%n
            current_pos_clause = all_states[t][num] == pos
            next_pos_same = all_states[t+1][num] == pos
            move_clauses = [generate_move_clause(t,i,"1","1"),generate_move_clause(t,i,"1","0"),
                            generate_move_clause(t,j,"0","1"),generate_move_clause(t,j,"0","0")]
            s.add(Implies(current_pos_clause,Or([next_pos_same,]+move_clauses)))

    # move_clauses = []
    for (bool_inc,bool_row) in [("0","0"),("0","1"),("1","0"),("1","1")]:
        for i in range(n):
            move_clause = generate_move_clause(t, i, bool_row, bool_inc)
            is_inc = 1 if bool_inc == "1" else -1 # "1" - increment, "0" - decrement
            is_row = bool_row == "1" # "1" - row shift, "0" - column shift
            shift_clause = []
            
            for j in range(n):
                for num in range(n*n):
                    if is_row:
                        current_position = i*n+j
                        next_position = i*n+(j+is_inc)%n
                    else:
                        current_position = j*n+i
                        next_position = ((j+is_inc)%n)*n+i

                    current_pos_clause = all_states[t][num] == current_position
                    next_pos_clause = all_states[t+1][num] == next_position
                    shift_clause.append(Implies(current_pos_clause,next_pos_clause))

            s.add(Implies(move_clause,And(shift_clause)))

# Output the moves
x = s.check()
print(x)
if x == sat:
    m = s.model()
    moves = [{} for i in range(T)]
    for d in m.decls():
        if "move" in d.name():
            i = int(re.findall("move_[0-9]+",d.name())[0].strip("move_"))
            moves[i][d.name()]=m[d]
    for i in range(len(moves)):
        type_of_move = [["u","d"],["l","r"]][1 if moves[i][f"move_{i}_row_or_col"] else 0][1 if moves[i][f"move_{i}_inc_or_dec"] else 0]
        position_of_move = moves[i][f"move_{i}_pos"]
        a = position_of_move<IntVal(n)
        if eval(str(a)):
            print(f"{position_of_move}{type_of_move}")