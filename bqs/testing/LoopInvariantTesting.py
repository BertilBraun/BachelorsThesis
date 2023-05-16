import itertools
import math
import sys

STACK_SIZE = 10
DEPTH_STACK_SIZE = 10
IS_THRESH = 3

max_iters = {}


def quick_sort(array):
    original_begin = 0
    original_end = len(array)

    begin = original_begin
    end = original_end

    depth_limit = 2 * math.log2(end - begin) + 3
    stack = [0]*STACK_SIZE
    depth_stack = [0]*DEPTH_STACK_SIZE
    stack_pointer = 0
    depth_pointer = 0
    depth = 0

    stack[stack_pointer] = begin
    stack[stack_pointer + 1] = end
    stack_pointer += 2
    depth_stack[depth_pointer] = depth
    depth_pointer += 1

    iter = 0
    while stack_pointer > 0:
        # print all the variables
        # print("---------------------")
        # print("array", array)
        # print("original_begin", original_begin)
        # print("original_end", original_end)
        # print("begin", begin)
        # print("end", end)
        # print("depth_limit", depth_limit)
        # print("stack", stack)
        # print("depth_stack", depth_stack)
        # print("stack_pointer", stack_pointer)
        # print("depth_pointer", depth_pointer)
        # print("depth", depth)
        # print("iter", iter)
        # print("end - begin", end - begin)

        iter += 1
        max_iters[len(array)] = max(max_iters.get(len(array), 0), iter)

        if depth < depth_limit and (end - begin > IS_THRESH) and stack_pointer < STACK_SIZE:
            pivot = partition(array, begin, end)
            if pivot - begin > end - pivot:
                stack[stack_pointer] = begin
                stack[stack_pointer + 1] = pivot
                begin = pivot + 1
            else:
                stack[stack_pointer] = pivot + 1
                stack[stack_pointer + 1] = end
                end = pivot
            stack_pointer += 2
            depth += 1
            depth_stack[depth_pointer] = depth
            depth_pointer += 1
        else:
            insertion_sort(array, begin, end)
            stack_pointer -= 2
            begin = stack[stack_pointer]
            end = stack[stack_pointer + 1]
            depth_pointer -= 1
            depth = depth_stack[depth_pointer]


def partition(array, begin, end):
    pivot = array[end - 1]
    i = begin - 1
    for j in range(begin, end - 1):
        if array[j] <= pivot:
            i += 1
            array[i], array[j] = array[j], array[i]
    array[i + 1], array[end - 1] = array[end - 1], array[i + 1]
    return i + 1


def insertion_sort(array, begin, end):
    for i in range(begin + 1, end):
        key = array[i]
        j = i - 1
        while j >= begin and key < array[j]:
            array[j + 1] = array[j]
            j -= 1
        array[j + 1] = key


# run quick_sort on all possible arrays of length 1 to 10
for i in range(1, 12):
    for permutation in itertools.permutations(range(i)):
        quick_sort(list(permutation))

# print the maximum number of iterations for each array length
for i in range(1, 11):
    print(i, max_iters[i])

sys.exit(0)

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
