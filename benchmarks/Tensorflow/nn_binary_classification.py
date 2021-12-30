import os
import json
import tensorflow as tf
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

num_epochs = 30
num_steps_per_epoch=70
data_size = 1000
feature_size = 2

def read_file(filename, cols):
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
			n2 = int(nums[1])
			tmp[n1] = n2
	return np.array(tmp)

def get_dataset():
	X_train = read_file('X_train.txt', 3)
	y_train = read_file('y_train.txt', 2)
	X_test = read_file('X_test.txt', 3)
	y_test = read_file('y_test.txt', 2)
	return X_train, y_train, X_test, y_test

def build_and_compile_model(train_features):
	normalizer = tf.keras.layers.Normalization(axis=-1)
	normalizer.adapt(np.array(train_features))
	model = tf.keras.Sequential([
		normalizer,
		layers.Dense(25, activation='relu'),
		layers.Dense(1, activation='sigmoid')
	])

	model.compile(
    	loss='binary_crossentropy',
    	optimizer=tf.optimizers.RMSprop(learning_rate=0.01),
    	metrics=['accuracy'])
	return model

# Define Strategy
strategy = tf.distribute.MultiWorkerMirroredStrategy()
print('Number of devices: {}'.format(strategy.num_replicas_in_sync))
X_train, y_train, X_test, y_test = get_dataset()

with strategy.scope():
	multi_worker_model = build_and_compile_model(X_train)

history = multi_worker_model.fit(
    X_train,
    y_train,
    epochs=num_epochs,
    # Suppress logging.
    verbose=2)

test_results = multi_worker_model.evaluate(X_test, y_test, verbose=2)

