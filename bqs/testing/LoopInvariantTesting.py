array = [0, 1, 1, 2, 3, 3]
indexL = [1, 0]
indexR = [0, 1]
numLeft = 0
numRight = 1
startLeft = 2
startRight = 1
begin = 2
last = 4
originalEnd = 6
originalBegin = 0
pivot = 3
BLOCKSIZE = 2

print(R"""
(startRight < BLOCKSIZE && startRight + numRight < BLOCKSIZE) ==> 
 (\forall int i; last - indexR[startRight + numRight] < i < originalEnd; 
  (\exists int j; 0 <= j < numRight; indexR[startRight + j] == i - last) ? 
   array[i] <= pivot : pivot <= array[i]
 );
""")

if startRight < BLOCKSIZE and startRight + numRight < BLOCKSIZE:
    for i in range(last - indexR[startRight + numRight] + 1, originalEnd):
        for j in range(numRight):
            if indexR[startRight + j] == i - last:
                print("exists", i, j, "array[i]", array[i], "array[i] <= pivot", array[i] <= pivot)
                break
        else:
            print("not exists", i, "array[i]", array[i], "pivot <= array[i]", pivot <= array[i])

array = [0, 1, 1, 2, 3, 3]
indexL = [1, 0]
indexR = [0, 1]
numLeft = 0
numRight = 1
startLeft = 2
startRight = 1
begin = 2
last = 4
originalEnd = 6
originalBegin = 0
pivot = 3
BLOCKSIZE = 2


print(R"""
(numRight != 0) ==> (\forall int i; last - BLOCKSIZE < i < originalEnd; (\exists int j; 0 <= j < numRight; indexR[startRight + j] == last - i) ? array[i] <= pivot : pivot <= array[i])
""")

if numRight != 0:
    for i in range(last - BLOCKSIZE + 1, originalEnd):
        for j in range(numRight):
            print("i", i, "j", j, "indexR[startRight + j]", indexR[startRight + j], "last - i", last - i)
            if indexR[startRight + j] == last - i:
                print("exists", i, j, "array[i]", array[i], "array[i] <= pivot", array[i] <= pivot)
                break
        else:
            print("not exists", i, "array[i]", array[i], "pivot <= array[i]", pivot <= array[i])

array = [5, 3, 3, 5, 4, 2]
indexL = [0, 0]
indexR = [1, 1]
numLeft = 1
numRight = 0
startLeft = 0
startRight = 0
begin = 0
last = 2
originalEnd = 6
originalBegin = 0
pivot = 3
BLOCKSIZE = 2

print(R"""
(numLeft != 0) ==> (\forall int i; originalBegin <= i < begin + BLOCKSIZE; 
                    (\exists int j; 0 <= j < numLeft; indexL[startLeft + j] == i - begin) ? 
                     pivot <= array[i] : array[i] <= pivot
                   );
""")

if numLeft != 0:
    for i in range(originalBegin, begin + BLOCKSIZE):
        print("Iteration", i)
        for j in range(numLeft):
            if indexL[startLeft + j] == i - begin:
                print("exists", i, j, "array[i]", array[i], "pivot <= array[i]", pivot <= array[i])
                break
        else:
            print("not exists", i, "array[i]", array[i], "array[i] <= pivot", array[i] <= pivot)

array = [6, 5, 6, 1, 0, 4]
begin = 0
indexL = [0, 1]
indexR = [1, 1]
last = 4
num = 0
numLeft = 1
numRight = 0
startLeft = 0
startRight = 2
originalBegin = 0
originalEnd = 6
pivot = 4
BLOCKSIZE = 2

print(R"""
(numLeft == 0) ==> (\forall int i; originalBegin <= i < begin; array[i] <= pivot)
""")

if numLeft == 0:
    for i in range(originalBegin, begin):
        print("Iteration", i)
        print("array[i]", array[i], "pivot", pivot, "array[i] <= pivot", array[i] <= pivot)
