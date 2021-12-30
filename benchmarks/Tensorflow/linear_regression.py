import os
import json
import tensorflow as tf
from tensorflow import keras
from tensorflow.keras import layers
import numpy as np
from multiprocessing import util
import time
import sys
import matplotlib.pyplot as plt

os.environ["CUDA_VISIBLE_DEVICES"] = "-1"
os.environ.pop('TF_CONFIG', None)

tf_config = {
	'cluster': {
	    'worker': []
	},
	'task': {'type': 'worker', 'index': 0}
}
for i in range(len(sys.argv)-2):
	tf_config['cluster']['worker'].append(sys.argv[i+1])
tf_config['task']['index'] = int(sys.argv[-1])
os.environ['TF_CONFIG'] = json.dumps(tf_config)

num_epochs = 100
num_steps_per_epoch=70
data_size = 1000000
train_size = int(0.8*data_size)
test_size = data_size-train_size
feature_size = 100

def read_file(filename, data_size, cols):
	f = open(filename,'r')
	lines = f.readlines()
	tmp = [[0 for j in range(feature_size)] for i in range(data_size)]
	if(cols == 2):
		tmp = [ 0 for i in range(data_size)]
	for l in lines:
		nums = l.split(',')
		if(cols == 3):
			n1 = int(nums[0])
			n2 = int(nums[1])
			n3 = float(nums[2])
			tmp[n1][n2] = n3
		else:
			n1 = int(nums[0])
			n2 = float(nums[1])
			tmp[n1] = n2
	return np.array(tmp)

def get_dataset():
	X_train = read_file('lr_input3.txt', train_size, 3)
	y_train = read_file('lr_output3.txt', train_size, 2)
	X_test = read_file('lr_input4.txt', test_size, 3)
	y_test = read_file('lr_output4.txt', test_size, 2)
	return X_train, y_train, X_test, y_test

def build_and_compile_model(train_features):
	normalizer = layers.Normalization(axis=-1)
	normalizer.adapt(np.array(train_features))
	model = keras.Sequential([
		layers.Dense(100, activation='relu'),
		layers.Dense(1)
	])
	optimizer = tf.keras.optimizers.RMSprop(0.001)
	model.compile(loss='mse',
		        optimizer=optimizer,
		        metrics=['mae', 'mse'])
	return model

# Define Strategy
strategy = tf.distribute.MultiWorkerMirroredStrategy()
print('Number of devices: {}'.format(strategy.num_replicas_in_sync))
X_train, y_train, X_test, y_test = get_dataset()

with strategy.scope():
	model = build_and_compile_model(X_train)

early_stop = keras.callbacks.EarlyStopping(monitor='val_loss', patience=10)
start = time.time()
history = model.fit(X_train, y_train,
    epochs=num_epochs,
    validation_split = 0.2,
    verbose=2, callbacks=[early_stop])
end = time.time()
print("Time: ", end-start)

test_results = model.evaluate(X_test, y_test, verbose=2)

