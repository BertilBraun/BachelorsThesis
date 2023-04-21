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

"""
(startRight < BLOCKSIZE && startRight + numRight < BLOCKSIZE) ==> 
 (\forall int i; last - indexR[startRight + numRight] < i < originalEnd; 
  (\exists int j; 0 <= j < numRight; indexR[startRight + j] == i - last) ? 
   array[i] <= pivot : pivot <= array[i]
 );
"""

if startRight < BLOCKSIZE and startRight + numRight < BLOCKSIZE:
    for i in range(last - indexR[startRight + numRight] + 1, originalEnd):
        for j in range(numRight):
            if indexR[startRight + j] == i - last:
                print("exists", i, j, "array[i] <= pivot", array[i] <= pivot, "array[i]", array[i])
                break
        else:
            print("not exists", i, "pivot <= array[i]", pivot <= array[i], "array[i]", array[i])

"""
(numRight != 0) ==> (\forall int i; last - BLOCKSIZE < i < originalEnd; (\exists int j; 0 <= j < numRight; indexR[startRight + j] == last - i) ? array[i] <= pivot : pivot <= array[i])
"""

if numRight != 0:
    for i in range(last - BLOCKSIZE + 1, originalEnd):
        for j in range(numRight):
            print("i", i, "j", j, "indexR[startRight + j]", indexR[startRight + j], "last - i", last - i)
            if indexR[startRight + j] == last - i:
                print("exists", i, j, "array[i] <= pivot", array[i] <= pivot, "array[i]", array[i])
                break
        else:
            print("not exists", i, "pivot <= array[i]", pivot <= array[i], "array[i]", array[i])
