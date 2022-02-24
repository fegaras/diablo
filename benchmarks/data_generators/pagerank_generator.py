import random as rand

file1 = open('page-rank3.txt','w+')

x = 0
n = 30000
for i in range(n):
	for j in range(n):
		if(i == j):
			continue
		if(rand.random() > 0.01):
			continue
		if(x > 0):
			file1.write("\n")
		x += 1
		file1.write(str(i)+" "+str(j))
file1.close()
print(x)
