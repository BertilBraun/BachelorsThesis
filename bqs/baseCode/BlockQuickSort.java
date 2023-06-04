public class BlockQuickSort {

    private static final int BLOCKSIZE = 128;
    private static final int IS_THRESH = 16;
    private static final int STACK_SIZE = 80;
    private static final int DEPTH_STACK_SIZE = 40;

    public static int hoareBlockPartition(
            int[] array,
            int begin,
            int end,
            int pivotPosition) {
        int[] indexL = new int[BLOCKSIZE];
        int[] indexR = new int[BLOCKSIZE];

        int last = end - 1;
        int pivot = array[pivotPosition];
        swap(array, pivotPosition, last);
        pivotPosition = last;
        last--;

        int numLeft = 0;
        int numRight = 0;
        int startLeft = 0;
        int startRight = 0;
        int num = 0;

        while (last - begin + 1 > 2 * BLOCKSIZE) {
            if (numLeft == 0) {
                startLeft = 0;

                for (int j = 0; j < BLOCKSIZE; j++) {
                    indexL[numLeft] = j;
                    numLeft += array[begin + j] >= pivot ? 1 : 0;
                }
            }
            if (numRight == 0) {
                startRight = 0;

                for (int j = 0; j < BLOCKSIZE; j++) {
                    indexR[numRight] = j;
                    numRight += pivot >= array[last - j] ? 1 : 0;
                }
            }

            num = (numLeft < numRight) ? numLeft : numRight;
            for (int j = 0; j < num; j++) {
                swap(array, begin + indexL[startLeft + j], last - indexR[startRight + j]);
            }

            numLeft -= num;
            numRight -= num;
            startLeft += num;
            startRight += num;
            begin += (numLeft == 0) ? BLOCKSIZE : 0;
            last -= (numRight == 0) ? BLOCKSIZE : 0;
        }

        int shiftR = 0, shiftL = 0;
        if (numRight == 0 && numLeft == 0) {
            shiftL = ((last - begin) + 1) / 2;
            shiftR = (last - begin) + 1 - shiftL;
            startLeft = 0;
            startRight = 0;

            for (int j = 0; j < shiftL; j++) {
                indexL[numLeft] = j;
                numLeft += array[begin + j] >= pivot ? 1 : 0;
                indexR[numRight] = j;
                numRight += pivot >= array[last - j] ? 1 : 0;
            }
            if (shiftL < shiftR) {
                indexR[numRight] = shiftR - 1;
                numRight += pivot >= array[last - shiftR + 1] ? 1 : 0;
            }
        } else if (numRight != 0) {
            shiftL = (last - begin) - BLOCKSIZE + 1;
            shiftR = BLOCKSIZE;
            startLeft = 0;

            for (int j = 0; j < shiftL; j++) {
                indexL[numLeft] = j;
                numLeft += array[begin + j] >= pivot ? 1 : 0;
            }
        } else {
            shiftL = BLOCKSIZE;
            shiftR = (last - begin) - BLOCKSIZE + 1;
            startRight = 0;

            for (int j = 0; j < shiftR; j++) {
                indexR[numRight] = j;
                numRight += pivot >= array[last - j] ? 1 : 0;
            }
        }

        num = (numLeft < numRight) ? numLeft : numRight;
        for (int j = 0; j < num; j++) {
            swap(array, begin + indexL[startLeft + j], last - indexR[startRight + j]);
        }

        numLeft -= num;
        numRight -= num;
        startLeft += num;
        startRight += num;
        begin += (numLeft == 0) ? shiftL : 0;
        last -= (numRight == 0) ? shiftR : 0;

        if (numLeft != 0) {
            int lowerI = startLeft + numLeft - 1;
            int upper = last - begin;

            while (lowerI >= startLeft && indexL[lowerI] == upper) {
                upper--;
                lowerI--;
            }

            while (lowerI >= startLeft) {
                swap(array, begin + upper, begin + indexL[lowerI]);
                upper--;
                lowerI--;
            }

            swap(array, pivotPosition, begin + upper + 1);
            return begin + upper + 1;
        } else if (numRight != 0) {
            int lowerI = startRight + numRight - 1;
            int upper = last - begin;

            while (lowerI >= startRight && indexR[lowerI] == upper) {
                upper--;
                lowerI--;
            }

            while (lowerI >= startRight) {
                swap(array, last - upper, last - indexR[lowerI]);
                upper--;
                lowerI--;
            }

            swap(array, pivotPosition, last - upper);
            return last - upper;
        } else {
            swap(array, pivotPosition, begin);
            return begin;
        }
    }

    public static void quickSort(int[] array, int begin, int end) {
        int depthLimit = 2 * log2(end - begin + 1) + 3;
        int[] stack = new int[STACK_SIZE];
        int[] depthStack = new int[DEPTH_STACK_SIZE];
        int stackPointer = 0;
        int depthPointer = 0;
        int depth = 0;

        stack[stackPointer] = begin;
        stack[stackPointer + 1] = end;
        stackPointer += 2;
        depthStack[depthPointer] = depth;
        depthPointer++;

        while (stackPointer > 0) {
            if (depth < depthLimit && (end - begin > IS_THRESH)) {
                int pivot = partition(array, begin, end);
                if (pivot - begin > end - pivot - 1) {
                    stack[stackPointer] = begin;
                    stack[stackPointer + 1] = pivot;
                    begin = pivot + 1;
                } else {
                    stack[stackPointer] = pivot + 1;
                    stack[stackPointer + 1] = end;
                    end = pivot;
                }
                stackPointer += 2;
                depth++;
                depthStack[depthPointer] = depth;
                depthPointer++;
            } else {
                insertionSort(array, begin, end);
                stackPointer -= 2;
                begin = stack[stackPointer];
                end = stack[stackPointer + 1];
                depthPointer--;
                depth = depthStack[depthPointer];
            }
        }
    }

    public static void insertionSort(int[] array, int begin, int end) {
        for (int i = begin; i < end; i++) {
            int j = i;
            while (j > begin && array[j - 1] > array[j]) {
                swap(array, j, j - 1);
                j--;
            }
        }
    }

    public static void swap(int[] array, int i, int j) {
        int temp = array[i];
        array[i] = array[j];
        array[j] = temp;
    }

    public static void sortPair(int i1, int i2, int[] array) {
        if (array[i1] > array[i2]) {
            swap(array, i1, i2);
        }
    }

    public static int medianOf3(int[] array, int begin, int end) {
        int mid = begin + ((end - begin) / 2);
        sortPair(begin, mid, array);
        sortPair(mid, end - 1, array);
        sortPair(begin, mid, array);
        return mid;
    }

    public static int partition(int[] array, int begin, int end) {
        int mid = medianOf3(array, begin, end);
        return hoareBlockPartition(array, begin + 1, end - 1, mid);
    }

    public static int log2(int n) {
        if (n <= 0) {
            throw new IllegalArgumentException("Input must be a positive integer.");
        }

        int log2Value = 0;
        while (n > 1) {
            n /= 2;
            log2Value++;
        }

        return log2Value;
    }
}
