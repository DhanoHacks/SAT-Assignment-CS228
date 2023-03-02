### TEAM MEMBERS
## MEMBER 1: 210050040
## MEMBER 2: 210050044
## MEMBER 3: 210050155


from z3 import *
import sys
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
        one_pos = Int(f"board_{t}_pos_{i}_num")
        one_state.append(one_pos)
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
        s.add(all_states[t][i*n+j]==matrix[i][j])

# clause for win condition of game
t = T
win_state = []
for pos in range(n*n):
    s.add(all_states[t][pos]==pos+1)

# clauses for changing state of board by applying a move
for t in range(T):
    for pos in range(n*n):
        i = pos//n
        j = pos%n
        move_clauses = [generate_move_clause(t,i,"1","1"),generate_move_clause(t,i,"1","0"),
                        generate_move_clause(t,j,"0","1"),generate_move_clause(t,j,"0","0")]
        s.add(Or([all_states[t][pos]==all_states[t+1][pos],]+move_clauses))
for t in range(T):
    for (bool_inc,bool_row) in [("0","0"),("0","1"),("1","0"),("1","1")]:
        for i in range(n):
            move_clause = generate_move_clause(t, i, bool_row, bool_inc)
            is_inc = 1 if bool_inc == "1" else -1 # "1" - increment, "0" - decrement
            is_row = bool_row == "1" # "1" - row shift, "0" - column shift
            shift_clause = []
            for j in range(n):
                if is_row:
                    current_position = i*n+j
                    next_position = i*n+(j+is_inc)%n
                else:
                    current_position = j*n+i
                    next_position = ((j+is_inc)%n)*n+i
                shift_clause.append(all_states[t][current_position]==all_states[t+1][next_position])
            for other_i in range(n):
                if other_i==i:
                    continue
                for other_j in range(n):
                    if is_row:
                        shift_clause.append(all_states[t][other_i*n+other_j]==all_states[t+1][other_i*n+other_j])
                    else:
                        shift_clause.append(all_states[t][other_i+other_j*n]==all_states[t+1][other_i+other_j*n])
            s.add(Implies(move_clause,And(shift_clause)))

# Output the moves
x = s.check()
print(x)
if x == sat:
    m = s.model()
    moves = [{} for t in range(T)]
    for d in m.decls():
        if "move" in d.name():
            t = int(d.name().split("_")[1])
            moves[t][d.name()]=m[d]
    for t in range(len(moves)):
        type_of_move = [["u","d"],["l","r"]][1 if moves[t][f"move_{t}_row_or_col"] else 0][1 if moves[t][f"move_{t}_inc_or_dec"] else 0]
        position_of_move = moves[t][f"move_{t}_pos"]
        a = position_of_move<IntVal(n)
        if eval(str(a)):
            print(f"{position_of_move}{type_of_move}")