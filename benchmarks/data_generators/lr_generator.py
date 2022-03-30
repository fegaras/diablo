import time
import random as rand
import numpy as np
from sklearn import datasets

def createDataset(X, y, n, m, f1, f2):
	file1 = open(f1,'w+')
	file2 = open(f2,'w+')
	start = time.time()
	for i in range(n):
		file1.write(str(i)+","+str(0)+","+str(1)+"\n")
		for j in range(m):
			file1.write(str(i)+","+str(j+1)+","+str(X[i][j]))
			if(i < n-1 or j < m-1):
				file1.write("\n")
		file2.write(str(i)+","+str(y[i]))
		if(i%1000==0):
			print("Time: ",time.time()-start," i:", i) 
		if(i < n-1):
			file2.write("\n")
	file1.close()
	file2.close()

data_size = 10000
train_size = int(0.8*data_size)
ft_size = 100
X, y = datasets.make_regression(n_samples=data_size, n_features=ft_size, shuffle=True)
createDataset(X[:train_size], y[:train_size], train_size, ft_size, 'lr_input1.txt', 'lr_output1.txt')
createDataset(X[train_size:], y[train_size:], data_size-train_size, ft_size, 'lr_input2.txt', 'lr_output2.txt')
