### TEAM MEMBERS
## MEMBER 1: <roll_number_1>
## MEMBER 2: <roll_number_2>
## MEMBER 3: <roll_number_3>


from z3 import *
import sys

file = sys.argv[1]

with open(file) as f:
	n,T = [int(x) for x in next(f).split()]
	matrix = []
	for line in f:
		matrix.append([int(x) for x in line.split()])

p = [] # row
q = [] # column

for i in range(n**2+1):
	p.append([])
	q.append([])
	for j in range(n):
		p[i].append([])
		q[i].append([])
		for t in range(T+1):
			p[i][j].append(Bool(f'p{i+1}_{j}_{t}'))
			q[i][j].append(Bool(f'q{i+1}_{j}_{t}'))

# Set s to the required formula
s = Solver()
for i in range(n):
	for j in range(n):
		value = matrix[i][j]
		s.add(p[value-1][i][0])
		s.add(q[value-1][j][0])

for t in range(T):
	for i in range(n**2):
		for j in range(n):
			phi = Not(p[i][j][t])
			andd = And(True,True)
			qhi = Not(q[i][j][t])
			qandd = And(True,True)
			for j2 in range(n):
				if( j2 == j):
					continue
				andd = And(andd, Not(p[i][j2][t]))
				qandd = And(qandd, Not(q[i][j2][t]))
			phi = Or(phi, andd)
			qhi = Or(qhi, qandd)
			s.add(phi)
			s.add(qhi)





x = s.check()
print(x)
if x == sat:
	m = s.model()
	
	
	# Output the moves