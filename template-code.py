### TEAM MEMBERS
## MEMBER 1: <roll_number_1>
## MEMBER 2: <roll_number_2>
## MEMBER 3: <roll_number_3>


from z3 import *
import sys
import math
file = sys.argv[1]

with open(file) as f:
	n,T = [int(x) for x in next(f).split()]
	matrix = []
	for line in f:
		matrix.append([int(x) for x in line.split()])

p = [] # row
q = [] # column
up = [] # shift, 0 = up, 1 = right, 2 = down, 3 = left
right = []
down = []
left = []

done = []
for i in range(n**2+1):
	p.append([])
	q.append([])
	for j in range(n):
		p[i].append([])
		q[i].append([])
		for t in range(T+1):
			p[i][j].append(Bool(f'p{i+1}_{j}_{t}'))
			q[i][j].append(Bool(f'q{i+1}_{j}_{t}'))


for j in range(n):
	up.append([])
	down.append([])
	right.append([])
	left.append([])
	
	for t in range(T):
		up[j].append(Bool(f'up_{j}_{t+1}'))
		down[j].append(Bool(f'down_{j}_{t+1}'))
		right[j].append(Bool(f'right_{j}_{t+1}'))
		left[j].append(Bool(f'left_{j}_{t+1}'))

for t in range(T+1):
	done.append(Bool(f"done_{t}"))
	
# Set s to the required formula
s = Solver()

# Input
for i in range(n):
	for j in range(n):
		value = matrix[i][j]
		s.add(p[value-1][i][0])
		s.add(q[value-1][j][0])

# Structural constraint
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

for t in range(T):
	# up ke lie
	upt = And(True, True)
	for j in range(n):
		sameCol = And(True, True)
		Row = And(True,True)
		for i in range(n**2):
			sameRowi = And(True, True)
			diffRowi = And(True, True)
			for a in range(n):
				phi = Or(Not(q[i][a][t]), q[i][a][t+1])
				sameCol = And(phi, sameCol)

				phi1 = Or(Not(p[i][a][t]), p[i][(a-1)%n][t+1])
				diffRowi = And(diffRowi, phi1)

				phi2 = Or(Not(p[i][a][t]), p[i][a][t+1])
				sameRowi = And(sameRowi, phi2)
			diffRowi = Or(Not(q[i][j][t]), diffRowi)
			sameRowi = Or(q[i][j][t], sameRowi)
			Row = And(Row, diffRowi, sameRowi)
		upj=And(sameCol, Row)
		upt = And(upt, upj)

	downt = And(True, True)
	for j in range(n):
		sameCol = And(True, True)
		Row = And(True,True)
		for i in range(n**2):
			sameRowi = And(True, True)
			diffRowi = And(True, True)
			for a in range(n):
				phi = Or(Not(q[i][a][t]), q[i][a][t+1])
				sameCol = And(phi, sameCol)

				phi1 = Or(Not(p[i][a][t]), p[i][(a+1)%n][t+1])
				diffRowi = And(diffRowi, phi1)

				phi2 = Or(Not(p[i][a][t]), p[i][a][t+1])
				sameRowi = And(sameRowi, phi2)
			diffRowi = Or(Not(q[i][j][t]), diffRowi)
			sameRowi = Or(q[i][j][t], sameRowi)
			Row = And(Row, diffRowi, sameRowi)
		downj=And(sameCol, Row)
		downt = And(downt, downj)

	leftt = And(True, True)
	for j in range(n):
		sameRow = And(True, True)
		Col = And(True,True)
		for i in range(n**2):
			sameColi = And(True, True)
			diffColi = And(True, True)
			for a in range(n):
				phi = Or(Not(p[i][a][t]), p[i][a][t+1])
				sameRow = And(phi, sameRow)

				phi1 = Or(Not(q[i][a][t]), q[i][(a-1)%n][t+1])
				diffColi = And(diffColi, phi1)

				phi2 = Or(Not(q[i][a][t]), q[i][a][t+1])
				sameColi = And(sameColi, phi2)
			diffColi = Or(Not(p[i][j][t]), diffColi)
			sameColi = Or(p[i][j][t], sameColi)
			Col = And(Col, diffColi, sameColi)
		leftj=And(sameRow, Col)
		leftt = And(leftt, leftj)

	rightt = And(True, True)
	for j in range(n):
		sameRow = And(True, True)
		Col = And(True,True)
		for i in range(n**2):
			sameColi = And(True, True)
			diffColi = And(True, True)
			for a in range(n):
				phi = Or(Not(p[i][a][t]), p[i][a][t+1])
				sameRow = And(phi, sameRow)

				phi1 = Or(Not(q[i][a][t]), q[i][(a+1)%n][t+1])
				diffColi = And(diffColi, phi1)

				phi2 = Or(Not(q[i][a][t]), q[i][a][t+1])
				sameColi = And(sameColi, phi2)
			diffColi = Or(Not(p[i][j][t]), diffColi)
			sameColi = Or(p[i][j][t], sameColi)
			Col = And(Col, diffColi, sameColi)
		rightj=And(sameRow, Col)
		rightt = And(rightt, rightj)
	s.add(Or(upt, rightt, downt, leftt))




for t in range(T):
	atleast1 = Or(False, False)
	no2 = And(True, True)
	none = And(True,True)
	for i in range(4*n):
		nocl = Or(False, False)
		if(i < n):
			atleast1= Or(atleast1, up[i%n][t])
			nocl = Or(nocl, Not(up[i%n][t]))
			none = And(none, Not(up[i%n][t]))
		elif (i < 2*n):
			atleast1= Or(atleast1, down[i%n][t])
			nocl = Or(nocl, Not(down[i%n][t]))
			none = And(none, Not(down[i%n][t]))
		elif (i < 3*n):
			atleast1= Or(atleast1, left[i%n][t])
			nocl = Or(nocl, Not(left[i%n][t]))
			none = And(none, Not(left[i%n][t]))
		else:
			atleast1= Or(atleast1, right[i%n][t])
			nocl = Or(nocl, Not(right[i%n][t]))
			none = And(none, Not(right[i%n][t]))
		for j in range(i+1, 4*n):
			if(j < n):
				nocl = Or(nocl, Not(up[j%n][t]))
			elif (j < 2*n):
				nocl = Or(nocl, Not(down[j%n][t]))
			elif (j < 3*n):
				nocl = Or(nocl, Not(left[j%n][t]))
			else:
				nocl = Or(nocl, Not(right[j%n][t]))
			no2 = And(no2, nocl)
	exactly1 = And(atleast1, no2)
	s.add(
		And
		(
		Or
   (Not(done[t]), none), 
   Or
   (done[t], exactly1)))	

atleastdone = Or(False, False)
for t in range(T+1):
	correct = And(True,True)
	for i in range(n**2):
		correct = And(correct, q[i][(i)%n][t], p[i][math.floor((i)/n)][t])
	correct = Or(Not(done[t]), correct)
	s.add(correct)
	atleastdone = Or(atleastdone, done[t])
s.add(atleastdone)



x = s.check()
print(x)
if x == sat:
	m = s.model()
	print(m)

	
	# Output the moves