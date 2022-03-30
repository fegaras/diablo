from sklearn.datasets import make_blobs
from sklearn.model_selection import train_test_split

N_SAMPLES = 100000
feature_size = 100
TEST_SIZE = 0.2
X, y = make_blobs(n_samples=N_SAMPLES, centers=2, n_features=feature_size,random_state=100)
X_train, X_test, y_train, y_test = train_test_split(X, y, test_size=TEST_SIZE, random_state=42)
f = open('X_train.txt','w+')
for i in range(len(X_train)):
	f.write(str(i)+','+str(0)+','+str(1)+'\n')
	for j in range(feature_size):
		f.write(str(i)+','+str(j+1)+','+str(X_train[i][j])+'\n')
f = open('X_test.txt','w+')
for i in range(len(X_test)):
	f.write(str(i)+','+str(0)+','+str(1)+'\n')
	for j in range(feature_size):
		f.write(str(i)+','+str(j+1)+','+str(X_test[i][j])+'\n')
f = open('y_train.txt','w+')
for i in range(len(y_train)):
	f.write(str(i)+','+str(y_train[i])+'\n')
f = open('y_test.txt','w+')
for i in range(len(y_test)):
	f.write(str(i)+','+str(y_test[i])+'\n')


