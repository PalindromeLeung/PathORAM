# Path ORAM 
from collections import defaultdict, deque

class Node(object): 
	def __init__(self, ary, idx, left, right): 
		self.val = ary
		self.idx = idx
		self.left = left 
		self.right = right


# constructing a simple binary tree
# actually each of the int in the arrary should be a pointer to a block of size B
#    0 
#   /\
#  1  2
#  /\ /\
# 3 4 5 6

n3 = Node([3,0,0,0], 3, None, None) 
n4 = Node([4,0,0,0], 4, None, None)
n5 = Node([5,0,0,0], 5, None, None)
n6 = Node([6,0,0,0], 6, None, None)

n1 = Node([1,0,0,0], 1, n3, n4)
n2 = Node([2,0,0,0], 2, n5, n6)

n0 = Node([0,0,0,0], 0, n1, n2)

def getHeight(root):
	if not root: 
		return 0 

	leftHeight = getHeight(root.left)
	rightHeight = getHeight(root.right) 

	return max(leftHeight, rightHeight) + 1 

print(getHeight(n0))

# should I assume that this is a perfect btree? No 
def getPath(root, NodeVal, pathList): 
	if not root:
		return False
	
	if root.val == NodeVal:
		return True 

	if (getPath(root.left, NodeVal) or getPath(root.right, NodeVal)):
		pathList.append(root.val) 
		return True 
	
	return False 

# P(x, l) = node.idx 
def getNode(root, index, currlevel, tgtlevel): 
	if not root:
		return None 

	if root.val == index && currlevel == tgtlevel: 
		return root.idx 

	nextlevel = currlevel + 1

	if(getNode(root.left, index, nextlevel, tgtlevel)):
		return getNode(root.left, index, nextlevel, tgtlevel)

	if(getNode(root.right, index, nextlevel, tgtlevel)):
		return getNode(root.right, index, nextlevel, tgtlevel)

	return None

def getCandidateBlocks(root, currleaf, blockID, level): 
	lhs = getNode(root, currleaf, 0, level)
	rhs = getNode(root, position[blockID], level)
	if lhs == rhs:
		return (blockID, getNodeVal(blockID))

	else:
		return None 

LEVELS = getHeight(n0)
N = 28 
Z = 4 # Z numbers of blocks within each bucket
stash = []
position = defaultdict(int, {k:random.randrange(0, (pow(2, LEVELS) - 1)) for k in range(N)})



def access(opCode, blockId, dataNew): 
	leafIdx = position[blockId]
	position[blockId] = random.randrange(0, (pow(2, LEVELS) - 1))

	# S (Read Path of leaf x at all levels) 
	# Is stash a global var? 
	
	for l in range(LEVELS):
		stash.append(getNode(n0, leafIdx, 0, l))

	# update block 
	for i in range(LEVELS):
		if stash[i].idx == leafIdx:
			dataOld = stash[i]

	if opCode == "wr" && (blockId <= N / Z): # assume blockId is valid or define the number of buckets
		# (check if the blockId is valid): do we assume a perfect binary tree? 
		stash = [item for item in stash if item not in[stash[blockId]]]
		stash[blockId] = dataNew

	# write path 
	for l in reversed(range(LEVELS)):
		# insert additional blocks from the stash to the path along the tree 
		candidateBlocks = []
		for idb in range(N):01
			candidateBlocks.append(getCandidateBlocks(leafIdx, idb, l))

		if (len(candidateBlocks) >= Z):
			writeBackSize = Z
		else:
			writeBackSize = len(candidateBlocks)

		writeBackBlocks = candidateBlocks[:writeBackSize]
		updatedStash = candidateBlocks[writeBackSize:]

		stash[l] = writeBackBlocks
	return dataOld
 
# What is a'? a' is another block ID should be in [0,N] and data' is the corresponding do
# how to design test cases? 



	

 
































