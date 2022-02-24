from sklearn.datasets import make_moons
from sklearn.model_selection import train_test_split

N_SAMPLES = 100000
TEST_SIZE = 0.2
X, y = make_moons(n_samples = N_SAMPLES, noise=0.2, random_state=100)
X_train, X_test, y_train, y_test = train_test_split(X, y, test_size=TEST_SIZE, random_state=42)
f = open('X_train.txt','w+')
for i in range(len(X_train)):
	f.write(str(i)+','+str(0)+','+str(X_train[i][0])+'\n')
	f.write(str(i)+','+str(1)+','+str(X_train[i][1])+'\n')
f = open('X_test.txt','w+')
for i in range(len(X_test)):
	f.write(str(i)+','+str(0)+','+str(X_test[i][0])+'\n')
	f.write(str(i)+','+str(1)+','+str(X_test[i][1])+'\n')
f = open('y_train.txt','w+')
for i in range(len(y_train)):
	f.write(str(i)+','+str(y_train[i])+'\n')
f = open('y_test.txt','w+')
for i in range(len(y_test)):
	f.write(str(i)+','+str(y_test[i])+'\n')


