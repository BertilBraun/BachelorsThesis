
import org.cprover.CProver;

public class BlockQuickSort {
    /*@
    public behavior
      assignable \nothing; 
      signals () false; 
   */

  public static BlockQuickSort BlockQuickSortSymb() {
    return new BlockQuickSort();

  }
  
  public static int hoareBlockPartitionSymb( 
  int[] array, int originalBegin, int originalEnd, int pivotPosition) {
    assert array != null;
    assert array.length < 500;
    assert (originalEnd - originalBegin) >= 1;
    assert (originalEnd - originalBegin) <= 500;
    assert 0 <= originalBegin;
    assert originalBegin < originalEnd;
    assert originalEnd <= array.length;
    assert originalBegin <= pivotPosition;
    assert pivotPosition < originalEnd;
    int quantVar0i = CProver.nondetInt();
    assert !(0 <= quantVar0i && quantVar0i < array.length) || 0 <= array[quantVar0i] && array[quantVar0i] <= array.length;
    int returnVar = CProver.nondetInt();
    int old0 = array.length;
    int old1 = array[pivotPosition];
    int[] old2 = new int[6];
    for (int i = originalBegin; i <= originalEnd - 1; ++i) {
      for (int j = originalBegin; j <= originalEnd - 1; ++j) {
        try {
          old2[j % 6] = array[j];

        } catch (java.lang.RuntimeException e) {

        }

      }

    }
    if (array != null) {
      for (int __tmpVar__0 = originalBegin; __tmpVar__0 <= originalEnd - 1; ++__tmpVar__0) {
        array[__tmpVar__0] = CProver.nondetInt();

      }

    }
    CProver.assume(array.length == old0);
    CProver.assume(originalBegin <= returnVar && returnVar < originalEnd);
    CProver.assume(array[returnVar] == old1);
    boolean b_0 = true;
    for (int quantVar1i = originalBegin; originalBegin <= quantVar1i && returnVar >= quantVar1i; ++quantVar1i) {
      b_0 = b_0 && array[quantVar1i] <= array[returnVar];

    }
    CProver.assume((b_0));
    boolean b_1 = true;
    for (int quantVar2i = returnVar; returnVar <= quantVar2i && originalEnd - 1 >= quantVar2i; ++quantVar2i) {
      b_1 = b_1 && array[returnVar] <= array[quantVar2i];

    }
    CProver.assume((b_1));
    int sum_0 = 0;
    int sum_1 = 0;
    boolean b_2 = true;
    for (int quantVar3i = originalBegin; originalBegin <= quantVar3i && originalEnd - 1 >= quantVar3i; ++quantVar3i) {
      for (int quantVar4j = originalBegin; originalBegin <= quantVar4j && originalEnd - 1 >= quantVar4j; ++quantVar4j) {
        sum_0 += array[quantVar3i] == array[quantVar4j] ? 1 : 0;

      }
      for (int quantVar5j = originalBegin; originalBegin <= quantVar5j && originalEnd - 1 >= quantVar5j; ++quantVar5j) {
        sum_1 += array[quantVar3i] == old2[quantVar5j % 6] ? 1 : 0;

      }
      b_2 = b_2 && ((sum_0) == (sum_1));

    }
    CProver.assume((b_2));
    return returnVar;

  }
  
  public static void quickSortRecImplSymb( 
  int[] array, int begin, int end, int depth, int depthLimit) {
    assert array != null;
    assert array.length < 500;
    assert 0 <= begin;
    assert begin <= end;
    assert end <= array.length;
    assert 0 <= depth;
    assert depth <= depthLimit;
    assert depthLimit < 500;
    int quantVar6i = CProver.nondetInt();
    assert !(0 <= quantVar6i && quantVar6i < array.length) || 0 <= array[quantVar6i] && array[quantVar6i] <= array.length;
    int old3 = array.length;
    int[] old4 = new int[6];
    for (int i = begin; i <= end - 1; ++i) {
      for (int j = begin; j <= end - 1; ++j) {
        try {
          old4[j % 6] = array[j];

        } catch (java.lang.RuntimeException e) {

        }

      }

    }
    if (array != null) {
      for (int __tmpVar__0 = begin; __tmpVar__0 <= end - 1; ++__tmpVar__0) {
        array[__tmpVar__0] = CProver.nondetInt();

      }

    }
    CProver.assume(array.length == old3);
    boolean b_3 = true;
    for (int quantVar7i = begin; begin <= quantVar7i && end - 1 - 1 >= quantVar7i; ++quantVar7i) {
      b_3 = b_3 && array[quantVar7i] <= array[quantVar7i + 1];

    }
    CProver.assume((b_3));
    int sum_2 = 0;
    int sum_3 = 0;
    boolean b_4 = true;
    for (int quantVar8i = begin; begin <= quantVar8i && end - 1 >= quantVar8i; ++quantVar8i) {
      for (int quantVar9j = begin; begin <= quantVar9j && end - 1 >= quantVar9j; ++quantVar9j) {
        sum_2 += array[quantVar8i] == array[quantVar9j] ? 1 : 0;

      }
      for (int quantVar10j = begin; begin <= quantVar10j && end - 1 >= quantVar10j; ++quantVar10j) {
        sum_3 += array[quantVar8i] == old4[quantVar10j % 6] ? 1 : 0;

      }
      b_4 = b_4 && ((sum_2) == (sum_3));

    }
    CProver.assume((b_4));

  }
  
  public static void insertionSortSymb( 
  int[] array, int begin, int end) {
    assert array != null;
    assert array.length < 500;
    assert 0 <= begin;
    assert begin <= end;
    assert end <= array.length;
    int old5 = array.length;
    int[] old6 = new int[6];
    for (int i = begin; i <= end - 1; ++i) {
      for (int j = begin; j <= end - 1; ++j) {
        try {
          old6[j % 6] = array[j];

        } catch (java.lang.RuntimeException e) {

        }

      }

    }
    if (array != null) {
      for (int __tmpVar__0 = begin; __tmpVar__0 <= end - 1; ++__tmpVar__0) {
        array[__tmpVar__0] = CProver.nondetInt();

      }

    }
    CProver.assume(array.length == old5);
    boolean b_5 = true;
    for (int quantVar11i = begin; begin <= quantVar11i && end - 1 - 1 >= quantVar11i; ++quantVar11i) {
      b_5 = b_5 && array[quantVar11i] <= array[quantVar11i + 1];

    }
    CProver.assume((b_5));
    int sum_4 = 0;
    int sum_5 = 0;
    boolean b_6 = true;
    for (int quantVar12i = begin; begin <= quantVar12i && end - 1 >= quantVar12i; ++quantVar12i) {
      for (int quantVar13j = begin; begin <= quantVar13j && end - 1 >= quantVar13j; ++quantVar13j) {
        sum_4 += array[quantVar12i] == array[quantVar13j] ? 1 : 0;

      }
      for (int quantVar14j = begin; begin <= quantVar14j && end - 1 >= quantVar14j; ++quantVar14j) {
        sum_5 += array[quantVar12i] == old6[quantVar14j % 6] ? 1 : 0;

      }
      b_6 = b_6 && ((sum_4) == (sum_5));

    }
    CProver.assume((b_6));

  }
  
  public static void swapSymb( 
  int[] array, int i, int j) {
    assert array != null;
    assert array.length < 500;
    assert 0 <= i;
    assert i < array.length;
    assert 0 <= j;
    assert j < array.length;
    int old7 = array.length;
    int old8 = array[j];
    int old9 = array[i];
    array[i] = CProver.nondetInt();
    array[j] = CProver.nondetInt();
    CProver.assume(array.length == old7);
    CProver.assume(array[i] == old8 && array[j] == old9);

  }
  
  public static void sortPairSymb(int i1, int i2,  
  int[] array) {
    assert array != null;
    assert array.length < 500;
    assert 0 <= i1;
    assert i1 < array.length;
    assert 0 <= i2;
    assert i2 < array.length;
    int old10 = array.length;
    int old11 = array[i1];
    int old12 = array[i2];
    array[i1] = CProver.nondetInt();
    array[i2] = CProver.nondetInt();
    CProver.assume(array.length == old10);
    CProver.assume((old11 <= old12) ? (array[i1] == old11 && array[i2] == old12) : (array[i1] == old12 && array[i2] == old11));

  }
  
  public static int medianOf3Symb( 
  int[] array, int begin, int end) {
    assert array != null;
    assert array.length < 500;
    assert end - begin >= 3;
    assert 0 <= begin;
    assert begin < end;
    assert end <= array.length;
    int returnVar = CProver.nondetInt();
    int old13 = array.length;
    int[] old14 = new int[6];
    for (int i = begin; i <= end - 1; ++i) {
      for (int j = begin; j <= end - 1; ++j) {
        try {
          old14[j % 6] = array[j];

        } catch (java.lang.RuntimeException e) {

        }

      }

    }
    array[begin] = CProver.nondetInt();
    array[begin + ((end - begin) / 2)] = CProver.nondetInt();
    array[end - 1] = CProver.nondetInt();
    CProver.assume(array.length == old13);
    CProver.assume(returnVar == begin + ((end - begin) / 2));
    CProver.assume(array[begin] <= array[returnVar] && array[returnVar] <= array[end - 1]);
    int sum_6 = 0;
    int sum_7 = 0;
    boolean b_7 = true;
    for (int quantVar15i = begin; begin <= quantVar15i && end - 1 >= quantVar15i; ++quantVar15i) {
      for (int quantVar16j = begin; begin <= quantVar16j && end - 1 >= quantVar16j; ++quantVar16j) {
        sum_6 += array[quantVar15i] == array[quantVar16j] ? 1 : 0;

      }
      for (int quantVar17j = begin; begin <= quantVar17j && end - 1 >= quantVar17j; ++quantVar17j) {
        sum_7 += array[quantVar15i] == old14[quantVar17j % 6] ? 1 : 0;

      }
      b_7 = b_7 && ((sum_6) == (sum_7));

    }
    CProver.assume((b_7));
    return returnVar;

  }
  
  public static int partitionSymb( 
  int[] array, int begin, int end) {
    assert array != null;
    assert array.length < 500;
    assert end - begin >= 3;
    assert 0 <= begin;
    assert begin < end;
    assert end <= array.length;
    int returnVar = CProver.nondetInt();
    int old15 = array.length;
    int[] old16 = new int[6];
    for (int i = begin; i <= end - 1; ++i) {
      for (int j = begin; j <= end - 1; ++j) {
        try {
          old16[j % 6] = array[j];

        } catch (java.lang.RuntimeException e) {

        }

      }

    }
    if (array != null) {
      for (int __tmpVar__0 = begin; __tmpVar__0 <= end - 1; ++__tmpVar__0) {
        array[__tmpVar__0] = CProver.nondetInt();

      }

    }
    CProver.assume(array.length == old15);
    CProver.assume(begin <= returnVar && returnVar < end);
    boolean b_8 = true;
    for (int quantVar18i = begin; begin <= quantVar18i && returnVar >= quantVar18i; ++quantVar18i) {
      b_8 = b_8 && array[quantVar18i] <= array[returnVar];

    }
    CProver.assume((b_8));
    boolean b_9 = true;
    for (int quantVar19i = returnVar; returnVar <= quantVar19i && end - 1 >= quantVar19i; ++quantVar19i) {
      b_9 = b_9 && array[returnVar] <= array[quantVar19i];

    }
    CProver.assume((b_9));
    int sum_8 = 0;
    int sum_9 = 0;
    boolean b_10 = true;
    for (int quantVar20i = begin; begin <= quantVar20i && end - 1 >= quantVar20i; ++quantVar20i) {
      for (int quantVar21j = begin; begin <= quantVar21j && end - 1 >= quantVar21j; ++quantVar21j) {
        sum_8 += array[quantVar20i] == array[quantVar21j] ? 1 : 0;

      }
      for (int quantVar22j = begin; begin <= quantVar22j && end - 1 >= quantVar22j; ++quantVar22j) {
        sum_9 += array[quantVar20i] == old16[quantVar22j % 6] ? 1 : 0;

      }
      b_10 = b_10 && ((sum_8) == (sum_9));

    }
    CProver.assume((b_10));
    return returnVar;

  }
  
  public static boolean permutationSymb( 
  int[] array1,  
  int[] array2, int begin, int end) {
    assert array1 != null;
    assert array2 != null;
    assert 0 <= begin;
    assert begin <= end;
    assert end <= array1.length;
    assert array1.length == array2.length;
    boolean returnVar = CProver.nondetBoolean();
    int old17 = array1.length;
    int old18 = array2.length;
    CProver.assume(array1.length == old17);
    CProver.assume(array2.length == old18);
    int sum_10 = 0;
    int sum_11 = 0;
    boolean b_11 = true;
    int quantVar26i = CProver.nondetInt();
    int sum_12 = 0;
    int sum_13 = 0;
    if (!!returnVar) {
      for (int quantVar23i = begin; begin <= quantVar23i && end - 1 >= quantVar23i; ++quantVar23i) {
        for (int quantVar24j = begin; begin <= quantVar24j && end - 1 >= quantVar24j; ++quantVar24j) {
          sum_10 += array1[quantVar23i] == array1[quantVar24j] ? 1 : 0;

        }
        for (int quantVar25j = begin; begin <= quantVar25j && end - 1 >= quantVar25j; ++quantVar25j) {
          sum_11 += array1[quantVar23i] == array2[quantVar25j] ? 1 : 0;

        }
        b_11 = b_11 && ((sum_10) == (sum_11));

      }

    }
    if (!returnVar || (b_11)) {
      if (begin <= quantVar26i && quantVar26i < end) {
        for (int quantVar27j = begin; begin <= quantVar27j && end - 1 >= quantVar27j; ++quantVar27j) {
          sum_12 += array1[quantVar26i] == array1[quantVar27j] ? 1 : 0;

        }
        for (int quantVar28j = begin; begin <= quantVar28j && end - 1 >= quantVar28j; ++quantVar28j) {
          sum_13 += array1[quantVar26i] == array2[quantVar28j] ? 1 : 0;

        }

      }

    }
    CProver.assume((!returnVar || (b_11)) && (begin <= quantVar26i && quantVar26i < end && !((sum_12) == (sum_13)) || returnVar));
    return returnVar;

  }
  
  public BlockQuickSort() {
    {

    }

  }
  private static final int BLOCKSIZE = 2;
  private static final int IS_THRESH = 3;
  private static final int STACK_SIZE = 80;
  
  public static int hoareBlockPartitionVerf( 
  int[] array, int originalBegin, int originalEnd, int pivotPosition) {
    {
      CProver.assume(array != null && array.length < 500);

    }
    {
      CProver.assume((originalEnd - originalBegin) >= 1 && (originalEnd - originalBegin) <= 500);

    }
    {
      CProver.assume(0 <= originalBegin && originalBegin < originalEnd && originalEnd <= array.length);

    }
    {
      CProver.assume(originalBegin <= pivotPosition && pivotPosition < originalEnd);

    }
    {
      boolean b_12 = true;
      for (int quantVar29i = 0; 0 <= quantVar29i && array.length - 1 >= quantVar29i; ++quantVar29i) {
        b_12 = b_12 && (0 <= array[quantVar29i] && array[quantVar29i] <= array.length);

      }
      CProver.assume((b_12));

    }
    int old19 = array.length;
    int old20 = array[pivotPosition];
    int[] old21 = new int[6];
    int[] old22 = array;
    for (int i = originalBegin; i <= originalEnd - 1; ++i) {
      for (int j = originalBegin; j <= originalEnd - 1; ++j) {
        try {
          old21[j % 6] = array[j];

        } catch (java.lang.RuntimeException e) {

        }

      }

    }
    int returnVar = 0;
    try {
      int[] $$param0 = null;
      int $$param1 = 0;
      int $$param2 = 0;
      int[] $$param3 = null;
      int $$param4 = 0;
      int $$param5 = 0;
      int[] $$param6 = null;
      int $$param7 = 0;
      int $$param8 = 0;
      int[] $$param9 = null;
      int $$param10 = 0;
      int $$param11 = 0;
      int[] $$param12 = null;
      int $$param13 = 0;
      int $$param14 = 0;
      int[] $$param15 = null;
      int $$param16 = 0;
      int $$param17 = 0;
      int[] $$param18 = null;
      int $$param19 = 0;
      int $$param20 = 0;
      int[] $$param21 = null;
      int $$param22 = 0;
      int $$param23 = 0;
       
      int[] indexL = new int[BLOCKSIZE];
       
      int[] indexR = new int[BLOCKSIZE];
       
      int[] originalArray = new int[array.length];
      for (int i = 0; i < array.length; ) {
        assert !false;
        originalArray[i] = array[i];
        i++;

      }
      assert !false;
      originalArray[array.length - 1] = originalArray[array.length - 1];
      int originalArrayLength = originalArray.length;
      int begin = originalBegin;
      int end = originalEnd;
      int last = end - 1;
      int pivot = array[pivotPosition];
      $$param0 = array;
      $$param1 = pivotPosition;
      $$param2 = last;
      assert !(true && (old22 != $$param0 || $$param1 > originalEnd - 1 || $$param1 < originalBegin)) : "Illegal assignment to array[i] conflicting with assignables array[originalBegin .. originalEnd - 1]";
      assert !(true && (old22 != $$param0 || $$param2 > originalEnd - 1 || $$param2 < originalBegin)) : "Illegal assignment to array[j] conflicting with assignables array[originalBegin .. originalEnd - 1]";
      swapSymb($$param0, $$param1, $$param2);
      assert !false;
      pivotPosition = last;
      last--;
      int numLeft = 0;
      int numRight = 0;
      int startLeft = 0;
      int startRight = 0;
      int num = 0;
      if (last >= begin) {
        int indexL0 = indexL[0];
        int indexR0 = indexR[0];
        int indexL1 = indexL[1];
        int indexR1 = indexR[1];
        int[] old23 = new int[6];
        int[] old24 = array;
        for (int i = originalBegin; i <= originalEnd - 1; ++i) {
          for (int j = originalBegin; j <= originalEnd - 1; ++j) {
            try {
              old23[j % 6] = array[j];

            } catch (java.lang.RuntimeException e) {

            }

          }

        }
        {
          int quantVar35i = CProver.nondetInt();
          int quantVar36i = CProver.nondetInt();
          int quantVar37i = CProver.nondetInt();
          int quantVar38i = CProver.nondetInt();
          int quantVar39i = CProver.nondetInt();
          int quantVar40i = CProver.nondetInt();
          int quantVar41i = CProver.nondetInt();
          int quantVar42i = CProver.nondetInt();
          int quantVar43i = CProver.nondetInt();
          int quantVar44i = CProver.nondetInt();
          int quantVar45i = CProver.nondetInt();
          int quantVar46i = CProver.nondetInt();
          int quantVar47i = CProver.nondetInt();
          int sum_16 = 0;
          int sum_17 = 0;
          {
            assert originalBegin <= begin;
            assert begin <= last;
            assert last < originalEnd - 1;

          }
          {
            assert 0 <= numLeft;
            assert numLeft <= BLOCKSIZE;

          }
          {
            assert 0 <= numRight;
            assert numRight <= BLOCKSIZE;

          }
          {
            assert 0 <= startLeft;
            assert startLeft <= BLOCKSIZE;
            assert startLeft + numLeft <= BLOCKSIZE;

          }
          {
            assert 0 <= startRight;
            assert startRight <= BLOCKSIZE;
            assert startRight + numRight <= BLOCKSIZE;

          }
          {
            assert 0 <= num;
            assert num <= BLOCKSIZE;

          }
          assert numRight == 0 || numLeft == 0;
          assert !(0 <= quantVar35i && quantVar35i < numLeft) || indexL[quantVar35i] <= last - begin;
          assert !(0 <= quantVar36i && quantVar36i < BLOCKSIZE) || 0 <= indexL[quantVar36i] && indexL[quantVar36i] < BLOCKSIZE;
          assert !(0 <= quantVar37i && quantVar37i < numLeft - 1) || indexL[quantVar37i] < indexL[quantVar37i + 1];
          assert !(0 <= quantVar38i && quantVar38i < numLeft) || pivot <= array[begin + indexL[startLeft + quantVar38i]];
          assert !(0 <= quantVar39i && quantVar39i < numRight) || indexR[quantVar39i] <= last - begin;
          assert !(0 <= quantVar40i && quantVar40i < BLOCKSIZE) || 0 <= indexR[quantVar40i] && indexR[quantVar40i] < BLOCKSIZE;
          assert !(0 <= quantVar41i && quantVar41i < numRight - 1) || indexR[quantVar41i] < indexR[quantVar41i + 1];
          assert !(0 <= quantVar42i && quantVar42i < numRight) || array[last - indexR[startRight + quantVar42i]] <= pivot;
          assert !(startLeft < BLOCKSIZE) || (!(originalBegin <= quantVar43i && quantVar43i < begin + indexL[startLeft]) || array[quantVar43i] <= pivot);
          assert !(startLeft == BLOCKSIZE) || (!(originalBegin <= quantVar44i && quantVar44i < begin) || array[quantVar44i] <= pivot);
          assert !(startRight < BLOCKSIZE) || (!(last - indexR[startRight] < quantVar45i && quantVar45i < originalEnd) || pivot <= array[quantVar45i]);
          assert !(startRight == BLOCKSIZE) || (!(last < quantVar46i && quantVar46i < originalEnd) || pivot <= array[quantVar46i]);
          if (!!(originalBegin <= quantVar47i && quantVar47i < originalEnd)) {
            for (int quantVar48j = originalBegin; originalBegin <= quantVar48j && originalEnd - 1 >= quantVar48j; ++quantVar48j) {
              sum_16 += array[quantVar47i] == array[quantVar48j] ? 1 : 0;

            }
            for (int quantVar49j = originalBegin; originalBegin <= quantVar49j && originalEnd - 1 >= quantVar49j; ++quantVar49j) {
              sum_17 += array[quantVar47i] == old23[quantVar49j % 6] ? 1 : 0;

            }

          }
          assert !(originalBegin <= quantVar47i && quantVar47i < originalEnd) || (sum_16) == (sum_17);

        }
        assert !(false && (old24 != array || originalEnd - 2 > originalEnd - 1 || originalBegin < originalBegin)) : "Illegal assignment to array[originalBegin .. originalEnd - 2] conflicting with assiganbles + array[originalBegin .. originalEnd - 1]";
        assert !(false && (old24 != indexL || BLOCKSIZE - 1 > originalEnd - 1 || 0 < originalBegin)) : "Illegal assignment to indexL[0 .. BLOCKSIZE - 1] conflicting with assiganbles + array[originalBegin .. originalEnd - 1]";
        assert !(false && (old24 != indexR || BLOCKSIZE - 1 > originalEnd - 1 || 0 < originalBegin)) : "Illegal assignment to indexR[0 .. BLOCKSIZE - 1] conflicting with assiganbles + array[originalBegin .. originalEnd - 1]";
        num = CProver.nondetInt();
        startRight = CProver.nondetInt();
        startLeft = CProver.nondetInt();
        numRight = CProver.nondetInt();
        numLeft = CProver.nondetInt();
        begin = CProver.nondetInt();
        last = CProver.nondetInt();
        if (indexR != null) {
          for (int __tmpVar__0 = 0; __tmpVar__0 <= BLOCKSIZE - 1; ++__tmpVar__0) {
            indexR[__tmpVar__0] = CProver.nondetInt();

          }

        }
        if (indexL != null) {
          for (int __tmpVar__0 = 0; __tmpVar__0 <= BLOCKSIZE - 1; ++__tmpVar__0) {
            indexL[__tmpVar__0] = CProver.nondetInt();

          }

        }
        if (array != null) {
          for (int __tmpVar__0 = originalBegin; __tmpVar__0 <= originalEnd - 2; ++__tmpVar__0) {
            array[__tmpVar__0] = CProver.nondetInt();

          }

        }
        indexL0 = CProver.nondetInt();
        indexR0 = CProver.nondetInt();
        indexL1 = CProver.nondetInt();
        indexR1 = CProver.nondetInt();
        int oldDecreasesClauseValue0 = last - begin;
        {
          boolean b_13 = true;
          boolean b_14 = true;
          boolean b_15 = true;
          boolean b_16 = true;
          boolean b_17 = true;
          boolean b_18 = true;
          boolean b_19 = true;
          boolean b_20 = true;
          boolean b_21 = true;
          boolean b_22 = true;
          boolean b_23 = true;
          boolean b_24 = true;
          int sum_18 = 0;
          int sum_19 = 0;
          boolean b_25 = true;
          CProver.assume(originalBegin <= begin && begin <= last && last < originalEnd - 1);
          CProver.assume(0 <= numLeft && numLeft <= BLOCKSIZE);
          CProver.assume(0 <= numRight && numRight <= BLOCKSIZE);
          CProver.assume(0 <= startLeft && startLeft <= BLOCKSIZE && startLeft + numLeft <= BLOCKSIZE);
          CProver.assume(0 <= startRight && startRight <= BLOCKSIZE && startRight + numRight <= BLOCKSIZE);
          CProver.assume(0 <= num && num <= BLOCKSIZE);
          CProver.assume(numRight == 0 || numLeft == 0);
          for (int quantVar50i = 0; 0 <= quantVar50i && numLeft - 1 >= quantVar50i; ++quantVar50i) {
            b_13 = b_13 && indexL[quantVar50i] <= last - begin;

          }
          CProver.assume((b_13));
          for (int quantVar51i = 0; 0 <= quantVar51i && BLOCKSIZE - 1 >= quantVar51i; ++quantVar51i) {
            b_14 = b_14 && (0 <= indexL[quantVar51i] && indexL[quantVar51i] < BLOCKSIZE);

          }
          CProver.assume((b_14));
          for (int quantVar52i = 0; 0 <= quantVar52i && numLeft - 1 - 1 >= quantVar52i; ++quantVar52i) {
            b_15 = b_15 && indexL[quantVar52i] < indexL[quantVar52i + 1];

          }
          CProver.assume((b_15));
          for (int quantVar53i = 0; 0 <= quantVar53i && numLeft - 1 >= quantVar53i; ++quantVar53i) {
            b_16 = b_16 && pivot <= array[begin + indexL[startLeft + quantVar53i]];

          }
          CProver.assume((b_16));
          for (int quantVar54i = 0; 0 <= quantVar54i && numRight - 1 >= quantVar54i; ++quantVar54i) {
            b_17 = b_17 && indexR[quantVar54i] <= last - begin;

          }
          CProver.assume((b_17));
          for (int quantVar55i = 0; 0 <= quantVar55i && BLOCKSIZE - 1 >= quantVar55i; ++quantVar55i) {
            b_18 = b_18 && (0 <= indexR[quantVar55i] && indexR[quantVar55i] < BLOCKSIZE);

          }
          CProver.assume((b_18));
          for (int quantVar56i = 0; 0 <= quantVar56i && numRight - 1 - 1 >= quantVar56i; ++quantVar56i) {
            b_19 = b_19 && indexR[quantVar56i] < indexR[quantVar56i + 1];

          }
          CProver.assume((b_19));
          for (int quantVar57i = 0; 0 <= quantVar57i && numRight - 1 >= quantVar57i; ++quantVar57i) {
            b_20 = b_20 && array[last - indexR[startRight + quantVar57i]] <= pivot;

          }
          CProver.assume((b_20));
          if (!!(startLeft < BLOCKSIZE)) {
            for (int quantVar58i = originalBegin; originalBegin <= quantVar58i && begin + indexL[startLeft] - 1 >= quantVar58i; ++quantVar58i) {
              b_21 = b_21 && array[quantVar58i] <= pivot;

            }

          }
          CProver.assume(!(startLeft < BLOCKSIZE) || (b_21));
          if (!!(startLeft == BLOCKSIZE)) {
            for (int quantVar59i = originalBegin; originalBegin <= quantVar59i && begin - 1 >= quantVar59i; ++quantVar59i) {
              b_22 = b_22 && array[quantVar59i] <= pivot;

            }

          }
          CProver.assume(!(startLeft == BLOCKSIZE) || (b_22));
          if (!!(startRight < BLOCKSIZE)) {
            for (int quantVar60i = last - indexR[startRight] + 1; last - indexR[startRight] + 1 <= quantVar60i && originalEnd - 1 >= quantVar60i; ++quantVar60i) {
              b_23 = b_23 && pivot <= array[quantVar60i];

            }

          }
          CProver.assume(!(startRight < BLOCKSIZE) || (b_23));
          if (!!(startRight == BLOCKSIZE)) {
            for (int quantVar61i = last + 1; last + 1 <= quantVar61i && originalEnd - 1 >= quantVar61i; ++quantVar61i) {
              b_24 = b_24 && pivot <= array[quantVar61i];

            }

          }
          CProver.assume(!(startRight == BLOCKSIZE) || (b_24));
          for (int quantVar62i = originalBegin; originalBegin <= quantVar62i && originalEnd - 1 >= quantVar62i; ++quantVar62i) {
            for (int quantVar63j = originalBegin; originalBegin <= quantVar63j && originalEnd - 1 >= quantVar63j; ++quantVar63j) {
              sum_18 += array[quantVar62i] == array[quantVar63j] ? 1 : 0;

            }
            for (int quantVar64j = originalBegin; originalBegin <= quantVar64j && originalEnd - 1 >= quantVar64j; ++quantVar64j) {
              sum_19 += array[quantVar62i] == old23[quantVar64j % 6] ? 1 : 0;

            }
            b_25 = b_25 && (sum_18) == (sum_19);

          }
          CProver.assume((b_25));

        }
        if (last - begin + 1 > 2 * BLOCKSIZE) {
          boolean did_run_loop = true;
          int lastNumLeft = numLeft;
          int lastNumRight = numRight;
           
          int[] lastArray = new int[array.length];
          for (int i = 0; i < array.length; ) {
            assert !false;
            lastArray[i] = array[i];
            i++;

          }
          assert !false;
          lastArray[array.length - 1] = lastArray[array.length - 1];
          int lastBegin = begin;
          int lastLast = last;
           
          int[] lastIndexL = new int[BLOCKSIZE];
          for (int i = 0; i < BLOCKSIZE; ) {
            assert !false;
            lastIndexL[i] = indexL[i];
            i++;

          }
          assert !false;
          lastIndexL[BLOCKSIZE - 1] = lastIndexL[BLOCKSIZE - 1];
           
          int[] lastIndexR = new int[BLOCKSIZE];
          for (int i = 0; i < BLOCKSIZE; ) {
            assert !false;
            lastIndexR[i] = indexR[i];
            i++;

          }
          assert !false;
          lastIndexR[BLOCKSIZE - 1] = lastIndexR[BLOCKSIZE - 1];
          int lastStartLeft = startLeft;
          int lastStartRight = startRight;
          int lastNum = num;
          assert !false;
          indexL0 = indexL[0];
          assert !false;
          indexR0 = indexR[0];
          assert !false;
          indexL1 = indexL[1];
          assert !false;
          indexR1 = indexR[1];
          if (numLeft == 0) {
            assert !false;
            startLeft = 0;
            for (int j = 0; j < BLOCKSIZE; ) {
              assert !false;
              indexL[numLeft] = j;
              numLeft += array[begin + j] >= pivot ? 1 : 0;
              j++;

            }

          }
          if (numRight == 0) {
            assert !false;
            startRight = 0;
            for (int j = 0; j < BLOCKSIZE; ) {
              assert !false;
              indexR[numRight] = j;
              numRight += pivot >= array[last - j] ? 1 : 0;
              j++;

            }

          }
          assert !false;
          num = (numLeft < numRight) ? numLeft : numRight;
          if (num > 0) {
            for (int j = 0; j < num; ) {
              $$param3 = array;
              $$param4 = begin + indexL[startLeft + j];
              $$param5 = last - indexR[startRight + j];
              assert !(true && (old24 != $$param3 || $$param4 > originalEnd - 2 || $$param4 < originalBegin) && (indexL != $$param3 || $$param4 > BLOCKSIZE - 1 || $$param4 < 0) && (indexR != $$param3 || $$param4 > BLOCKSIZE - 1 || $$param4 < 0)) : "Illegal assignment to array[i] conflicting with assignables array[originalBegin .. originalEnd - 2], indexL[0 .. BLOCKSIZE - 1], indexR[0 .. BLOCKSIZE - 1], last, begin, numLeft, numRight, startLeft, startRight, num";
              assert !(true && (old24 != $$param3 || $$param5 > originalEnd - 2 || $$param5 < originalBegin) && (indexL != $$param3 || $$param5 > BLOCKSIZE - 1 || $$param5 < 0) && (indexR != $$param3 || $$param5 > BLOCKSIZE - 1 || $$param5 < 0)) : "Illegal assignment to array[j] conflicting with assignables array[originalBegin .. originalEnd - 2], indexL[0 .. BLOCKSIZE - 1], indexR[0 .. BLOCKSIZE - 1], last, begin, numLeft, numRight, startLeft, startRight, num";
              swapSymb($$param3, $$param4, $$param5);
              j++;

            }

          }
          numLeft -= num;
          numRight -= num;
          startLeft += num;
          startRight += num;
          begin += (numLeft == 0) ? BLOCKSIZE : 0;
          last -= (numRight == 0) ? BLOCKSIZE : 0;
          {
            int quantVar65i = CProver.nondetInt();
            int quantVar66i = CProver.nondetInt();
            int quantVar67i = CProver.nondetInt();
            int quantVar68i = CProver.nondetInt();
            int quantVar69i = CProver.nondetInt();
            int quantVar70i = CProver.nondetInt();
            int quantVar71i = CProver.nondetInt();
            int quantVar72i = CProver.nondetInt();
            int quantVar73i = CProver.nondetInt();
            int quantVar74i = CProver.nondetInt();
            int quantVar75i = CProver.nondetInt();
            int quantVar76i = CProver.nondetInt();
            int quantVar77i = CProver.nondetInt();
            int sum_20 = 0;
            int sum_21 = 0;
            {
              assert originalBegin <= begin;
              assert begin <= last;
              assert last < originalEnd - 1;

            }
            {
              assert 0 <= numLeft;
              assert numLeft <= BLOCKSIZE;

            }
            {
              assert 0 <= numRight;
              assert numRight <= BLOCKSIZE;

            }
            {
              assert 0 <= startLeft;
              assert startLeft <= BLOCKSIZE;
              assert startLeft + numLeft <= BLOCKSIZE;

            }
            {
              assert 0 <= startRight;
              assert startRight <= BLOCKSIZE;
              assert startRight + numRight <= BLOCKSIZE;

            }
            {
              assert 0 <= num;
              assert num <= BLOCKSIZE;

            }
            assert numRight == 0 || numLeft == 0;
            assert !(0 <= quantVar65i && quantVar65i < numLeft) || indexL[quantVar65i] <= last - begin;
            assert !(0 <= quantVar66i && quantVar66i < BLOCKSIZE) || 0 <= indexL[quantVar66i] && indexL[quantVar66i] < BLOCKSIZE;
            assert !(0 <= quantVar67i && quantVar67i < numLeft - 1) || indexL[quantVar67i] < indexL[quantVar67i + 1];
            assert !(0 <= quantVar68i && quantVar68i < numLeft) || pivot <= array[begin + indexL[startLeft + quantVar68i]];
            assert !(0 <= quantVar69i && quantVar69i < numRight) || indexR[quantVar69i] <= last - begin;
            assert !(0 <= quantVar70i && quantVar70i < BLOCKSIZE) || 0 <= indexR[quantVar70i] && indexR[quantVar70i] < BLOCKSIZE;
            assert !(0 <= quantVar71i && quantVar71i < numRight - 1) || indexR[quantVar71i] < indexR[quantVar71i + 1];
            assert !(0 <= quantVar72i && quantVar72i < numRight) || array[last - indexR[startRight + quantVar72i]] <= pivot;
            assert !(startLeft < BLOCKSIZE) || (!(originalBegin <= quantVar73i && quantVar73i < begin + indexL[startLeft]) || array[quantVar73i] <= pivot);
            assert !(startLeft == BLOCKSIZE) || (!(originalBegin <= quantVar74i && quantVar74i < begin) || array[quantVar74i] <= pivot);
            assert !(startRight < BLOCKSIZE) || (!(last - indexR[startRight] < quantVar75i && quantVar75i < originalEnd) || pivot <= array[quantVar75i]);
            assert !(startRight == BLOCKSIZE) || (!(last < quantVar76i && quantVar76i < originalEnd) || pivot <= array[quantVar76i]);
            if (!!(originalBegin <= quantVar77i && quantVar77i < originalEnd)) {
              for (int quantVar78j = originalBegin; originalBegin <= quantVar78j && originalEnd - 1 >= quantVar78j; ++quantVar78j) {
                sum_20 += array[quantVar77i] == array[quantVar78j] ? 1 : 0;

              }
              for (int quantVar79j = originalBegin; originalBegin <= quantVar79j && originalEnd - 1 >= quantVar79j; ++quantVar79j) {
                sum_21 += array[quantVar77i] == old23[quantVar79j % 6] ? 1 : 0;

              }

            }
            assert !(originalBegin <= quantVar77i && quantVar77i < originalEnd) || (sum_20) == (sum_21);

          }
          {
            assert last - begin >= 0;
            assert last - begin < oldDecreasesClauseValue0;

          }
          CProver.assume(false);

        }

      }
      int shiftR = 0;
      int shiftL = 0;
      if (numRight == 0 && numLeft == 0) {
        assert !false;
        shiftL = ((last - begin) + 1) / 2;
        assert !false;
        shiftR = (last - begin) + 1 - shiftL;
        assert !false;
        startLeft = 0;
        assert !false;
        startRight = 0;
        for (int j = 0; j < shiftL; ) {
          assert !false;
          indexL[numLeft] = j;
          numLeft += array[begin + j] >= pivot ? 1 : 0;
          assert !false;
          indexR[numRight] = j;
          numRight += pivot >= array[last - j] ? 1 : 0;
          j++;

        }
        if (shiftL < shiftR) {
          assert !false;
          indexR[numRight] = shiftR - 1;
          numRight += pivot >= array[last - shiftR + 1] ? 1 : 0;

        }

      } else if (numRight != 0) {
        assert !false;
        shiftL = (last - begin) - BLOCKSIZE + 1;
        assert !false;
        shiftR = BLOCKSIZE;
        assert !false;
        startLeft = 0;
        for (int j = 0; j < shiftL; ) {
          assert !false;
          indexL[numLeft] = j;
          numLeft += array[begin + j] >= pivot ? 1 : 0;
          j++;

        }

      } else {
        assert !false;
        shiftL = BLOCKSIZE;
        assert !false;
        shiftR = (last - begin) - BLOCKSIZE + 1;
        assert !false;
        startRight = 0;
        for (int j = 0; j < shiftR; ) {
          assert !false;
          indexR[numRight] = j;
          numRight += pivot >= array[last - j] ? 1 : 0;
          j++;

        }

      }
      assert !false;
      num = (numLeft < numRight) ? numLeft : numRight;
      if (num > 0) {
        for (int j = 0; j < num; ) {
          $$param6 = array;
          $$param7 = begin + indexL[startLeft + j];
          $$param8 = last - indexR[startRight + j];
          assert !(true && (old22 != $$param6 || $$param7 > originalEnd - 1 || $$param7 < originalBegin)) : "Illegal assignment to array[i] conflicting with assignables array[originalBegin .. originalEnd - 1]";
          assert !(true && (old22 != $$param6 || $$param8 > originalEnd - 1 || $$param8 < originalBegin)) : "Illegal assignment to array[j] conflicting with assignables array[originalBegin .. originalEnd - 1]";
          swapSymb($$param6, $$param7, $$param8);
          j++;

        }

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
          $$param9 = array;
          $$param10 = begin + upper;
          $$param11 = begin + indexL[lowerI];
          assert !(true && (old22 != $$param9 || $$param10 > originalEnd - 1 || $$param10 < originalBegin)) : "Illegal assignment to array[i] conflicting with assignables array[originalBegin .. originalEnd - 1]";
          assert !(true && (old22 != $$param9 || $$param11 > originalEnd - 1 || $$param11 < originalBegin)) : "Illegal assignment to array[j] conflicting with assignables array[originalBegin .. originalEnd - 1]";
          swapSymb($$param9, $$param10, $$param11);
          upper--;
          lowerI--;

        }
        $$param12 = array;
        $$param13 = pivotPosition;
        $$param14 = begin + upper + 1;
        assert !(true && (old22 != $$param12 || $$param13 > originalEnd - 1 || $$param13 < originalBegin)) : "Illegal assignment to array[i] conflicting with assignables array[originalBegin .. originalEnd - 1]";
        assert !(true && (old22 != $$param12 || $$param14 > originalEnd - 1 || $$param14 < originalBegin)) : "Illegal assignment to array[j] conflicting with assignables array[originalBegin .. originalEnd - 1]";
        swapSymb($$param12, $$param13, $$param14);
        {
          returnVar = begin + upper + 1;
          throw new BlockQuickSort.ReturnException();

        }

      } else if (numRight != 0) {
        int lowerI = startRight + numRight - 1;
        int upper = last - begin;
        while (lowerI >= startRight && indexR[lowerI] == upper) {
          upper--;
          lowerI--;

        }
        while (lowerI >= startRight) {
          $$param15 = array;
          $$param16 = last - upper;
          $$param17 = last - indexR[lowerI];
          assert !(true && (old22 != $$param15 || $$param16 > originalEnd - 1 || $$param16 < originalBegin)) : "Illegal assignment to array[i] conflicting with assignables array[originalBegin .. originalEnd - 1]";
          assert !(true && (old22 != $$param15 || $$param17 > originalEnd - 1 || $$param17 < originalBegin)) : "Illegal assignment to array[j] conflicting with assignables array[originalBegin .. originalEnd - 1]";
          swapSymb($$param15, $$param16, $$param17);
          upper--;
          lowerI--;

        }
        $$param18 = array;
        $$param19 = pivotPosition;
        $$param20 = last - upper;
        assert !(true && (old22 != $$param18 || $$param19 > originalEnd - 1 || $$param19 < originalBegin)) : "Illegal assignment to array[i] conflicting with assignables array[originalBegin .. originalEnd - 1]";
        assert !(true && (old22 != $$param18 || $$param20 > originalEnd - 1 || $$param20 < originalBegin)) : "Illegal assignment to array[j] conflicting with assignables array[originalBegin .. originalEnd - 1]";
        swapSymb($$param18, $$param19, $$param20);
        {
          returnVar = last - upper;
          throw new BlockQuickSort.ReturnException();

        }

      } else {
        $$param21 = array;
        $$param22 = pivotPosition;
        $$param23 = begin;
        assert !(true && (old22 != $$param21 || $$param22 > originalEnd - 1 || $$param22 < originalBegin)) : "Illegal assignment to array[i] conflicting with assignables array[originalBegin .. originalEnd - 1]";
        assert !(true && (old22 != $$param21 || $$param23 > originalEnd - 1 || $$param23 < originalBegin)) : "Illegal assignment to array[j] conflicting with assignables array[originalBegin .. originalEnd - 1]";
        swapSymb($$param21, $$param22, $$param23);
        {
          returnVar = begin;
          throw new BlockQuickSort.ReturnException();

        }

      }

    } catch (BlockQuickSort.ReturnException ex) {

    }
    {
      assert array.length == old19;

    }
    {
      {
        assert originalBegin <= returnVar;
        assert returnVar < originalEnd;

      }

    }
    {
      assert array[returnVar] == old20;

    }
    {
      int quantVar30i = CProver.nondetInt();
      assert !(originalBegin <= quantVar30i && quantVar30i <= returnVar) || array[quantVar30i] <= array[returnVar];

    }
    {
      int quantVar31i = CProver.nondetInt();
      assert !(returnVar <= quantVar31i && quantVar31i < originalEnd) || array[returnVar] <= array[quantVar31i];

    }
    {
      int quantVar32i = CProver.nondetInt();
      int sum_14 = 0;
      int sum_15 = 0;
      if (!!(originalBegin <= quantVar32i && quantVar32i < originalEnd)) {
        for (int quantVar33j = originalBegin; originalBegin <= quantVar33j && originalEnd - 1 >= quantVar33j; ++quantVar33j) {
          sum_14 += array[quantVar32i] == array[quantVar33j] ? 1 : 0;

        }
        for (int quantVar34j = originalBegin; originalBegin <= quantVar34j && originalEnd - 1 >= quantVar34j; ++quantVar34j) {
          sum_15 += array[quantVar32i] == old21[quantVar34j % 6] ? 1 : 0;

        }

      }
      assert !(originalBegin <= quantVar32i && quantVar32i < originalEnd) || ((sum_14) == (sum_15));

    }
    return returnVar;

  }
    /*@
    public normal_behavior
      requires array != null && array.length < 500; 
      requires (originalEnd - originalBegin) >= 1 && (originalEnd - originalBegin) <= 500; 
      requires 0 <= originalBegin && originalBegin < originalEnd && originalEnd <= array.length; 
      requires originalBegin <= pivotPosition && pivotPosition < originalEnd; 
      requires (\forall int i; 0 <= i < array.length; 0 <= array[i] && array[i] <= array.length); 
      ensures array.length == \old(array.length); 
      ensures originalBegin <= \result && \result < originalEnd; 
      ensures array[\result] == \old(array[pivotPosition]); 
      ensures (\forall int i; originalBegin <= i <= \result; array[i] <= array[\result]); 
      ensures (\forall int i; \result <= i < originalEnd; array[\result] <= array[i]); 
      ensures (\forall int i; originalBegin <= i < originalEnd; ((\num_of int j; originalBegin <= j < originalEnd; array[i] == array[j]) == (\num_of int j; originalBegin <= j < originalEnd; array[i] == \old(array[j])))); 
      assignable array[originalBegin .. originalEnd - 1]; 
   */

  public static int hoareBlockPartition( 
  int[] array, int originalBegin, int originalEnd, int pivotPosition) {
     
    int[] indexL = new int[BLOCKSIZE];
     
    int[] indexR = new int[BLOCKSIZE];
     
    int[] originalArray = new int[array.length];
    for (int i = 0; i < array.length; i++) {
      originalArray[i] = array[i];

    }
    originalArray[array.length - 1] = originalArray[array.length - 1];
    int originalArrayLength = originalArray.length;
    int begin = originalBegin;
    int end = originalEnd;
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
    if (last >= begin) {
      int indexL0 = indexL[0];
      int indexR0 = indexR[0];
      int indexL1 = indexL[1];
      int indexR1 = indexR[1];
      //@ loop_invariant originalBegin <= begin && begin <= last && last < originalEnd - 1;
      //@ loop_invariant 0 <= numLeft && numLeft <= BLOCKSIZE;
      //@ loop_invariant 0 <= numRight && numRight <= BLOCKSIZE;
      //@ loop_invariant 0 <= startLeft && startLeft <= BLOCKSIZE && startLeft + numLeft <= BLOCKSIZE;
      //@ loop_invariant 0 <= startRight && startRight <= BLOCKSIZE && startRight + numRight <= BLOCKSIZE;
      //@ loop_invariant 0 <= num && num <= BLOCKSIZE;
      //@ loop_invariant numRight == 0 || numLeft == 0;
      //@ loop_invariant (\forall int i; 0 <= i < numLeft; indexL[i] <= last - begin);
      //@ loop_invariant (\forall int i; 0 <= i < BLOCKSIZE; 0 <= indexL[i] && indexL[i] < BLOCKSIZE);
      //@ loop_invariant (\forall int i; 0 <= i < numLeft - 1; indexL[i] < indexL[i + 1]);
      //@ loop_invariant (\forall int i; 0 <= i < numLeft; pivot <= array[begin + indexL[startLeft + i]]);
      //@ loop_invariant (\forall int i; 0 <= i < numRight; indexR[i] <= last - begin);
      //@ loop_invariant (\forall int i; 0 <= i < BLOCKSIZE; 0 <= indexR[i] && indexR[i] < BLOCKSIZE);
      //@ loop_invariant (\forall int i; 0 <= i < numRight - 1; indexR[i] < indexR[i + 1]);
      //@ loop_invariant (\forall int i; 0 <= i < numRight; array[last - indexR[startRight + i]] <= pivot);
      //@ loop_invariant startLeft < BLOCKSIZE ==> (\forall int i; originalBegin <= i < begin + indexL[startLeft]; array[i] <= pivot);
      //@ loop_invariant startLeft == BLOCKSIZE ==> (\forall int i; originalBegin <= i < begin; array[i] <= pivot);
      //@ loop_invariant startRight < BLOCKSIZE ==> (\forall int i; last - indexR[startRight] < i < originalEnd; pivot <= array[i]);
      //@ loop_invariant startRight == BLOCKSIZE ==> (\forall int i; last < i < originalEnd; pivot <= array[i]);
      //@ loop_invariant (\forall int i; originalBegin <= i < originalEnd; (\num_of int j; originalBegin <= j < originalEnd; array[i] == array[j]) == (\num_of int j; originalBegin <= j < originalEnd; array[i] == \old(array[j])));
      //@ loop_modifies array[originalBegin .. originalEnd - 2], last, begin, numLeft, numRight, startLeft, startRight, indexL[0 .. BLOCKSIZE - 1], indexR[0 .. BLOCKSIZE - 1], num;
      //@ loop_decreases last - begin;
      while (last - begin + 1 > 2 * BLOCKSIZE) {
        boolean did_run_loop = true;
        int lastNumLeft = numLeft;
        int lastNumRight = numRight;
         
        int[] lastArray = new int[array.length];
        for (int i = 0; i < array.length; i++) {
          lastArray[i] = array[i];

        }
        lastArray[array.length - 1] = lastArray[array.length - 1];
        int lastBegin = begin;
        int lastLast = last;
         
        int[] lastIndexL = new int[BLOCKSIZE];
        for (int i = 0; i < BLOCKSIZE; i++) {
          lastIndexL[i] = indexL[i];

        }
        lastIndexL[BLOCKSIZE - 1] = lastIndexL[BLOCKSIZE - 1];
         
        int[] lastIndexR = new int[BLOCKSIZE];
        for (int i = 0; i < BLOCKSIZE; i++) {
          lastIndexR[i] = indexR[i];

        }
        lastIndexR[BLOCKSIZE - 1] = lastIndexR[BLOCKSIZE - 1];
        int lastStartLeft = startLeft;
        int lastStartRight = startRight;
        int lastNum = num;
        indexL0 = indexL[0];
        indexR0 = indexR[0];
        indexL1 = indexL[1];
        indexR1 = indexR[1];
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
        if (num > 0) {
          for (int j = 0; j < num; j++) {
            swap(array, begin + indexL[startLeft + j], last - indexR[startRight + j]);

          }

        }
        numLeft -= num;
        numRight -= num;
        startLeft += num;
        startRight += num;
        begin += (numLeft == 0) ? BLOCKSIZE : 0;
        last -= (numRight == 0) ? BLOCKSIZE : 0;

      }

    }
    int shiftR = 0;
    int shiftL = 0;
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
    if (num > 0) {
      for (int j = 0; j < num; j++) {
        swap(array, begin + indexL[startLeft + j], last - indexR[startRight + j]);

      }

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
  
  public static void quickSortVerf( 
  int[] array, int begin, int end) {
    {
      CProver.assume(array != null && array.length < 500);

    }
    {
      CProver.assume(0 <= begin && begin < end && end <= array.length);

    }
    int old25 = array.length;
    int[] old26 = array;
    try {
      int[] $$param28 = null;
      int $$param29 = 0;
      int $$param30 = 0;
      int[] $$param31 = null;
      int $$param32 = 0;
      int $$param33 = 0;
       
      int[] stack = new int[STACK_SIZE];
      int top = 0;
      int depth = 0;
      int depthLimit = (int)(2 * log(end - begin) / log(2)) + 3;
      assert !false;
      stack[top++] = begin;
      assert !false;
      stack[top++] = end;
      while (top > 0) {
        assert !false;
        end = stack[--top];
        assert !false;
        begin = stack[--top];
        while (end - begin > IS_THRESH && depth < depthLimit) {
          $$param28 = array;
          $$param29 = begin;
          $$param30 = end;
          assert !(true && (old26 != $$param28 || $$param30 - 1 > $$param30 - 1 || $$param29 < $$param29)) : "Illegal assignment to array[begin .. end - 1] conflicting with assignables array[begin .. end - 1]";
          int pivot = partitionSymb($$param28, $$param29, $$param30);
          if (pivot - begin > end - pivot) {
            assert !false;
            stack[top++] = begin;
            assert !false;
            stack[top++] = pivot;
            assert !false;
            begin = pivot + 1;

          } else {
            assert !false;
            stack[top++] = pivot + 1;
            assert !false;
            stack[top++] = end;
            assert !false;
            end = pivot;

          }
          depth++;

        }
        if (end - begin <= IS_THRESH || depth >= depthLimit) {
          $$param31 = array;
          $$param32 = begin;
          $$param33 = end;
          assert !(true && (old26 != $$param31 || $$param33 - 1 > $$param33 - 1 || $$param32 < $$param32)) : "Illegal assignment to array[begin .. end - 1] conflicting with assignables array[begin .. end - 1]";
          insertionSortSymb($$param31, $$param32, $$param33);

        }
        depth--;

      }

    } catch (BlockQuickSort.ReturnException ex) {

    }
    {
      assert array.length == old25;

    }
    {
      int quantVar80i = CProver.nondetInt();
      assert !(begin <= quantVar80i && quantVar80i < end - 1) || array[quantVar80i] <= array[quantVar80i + 1];

    }
    {
      int[] $$param24 = null;
      int[] $$param25 = null;
      int $$param26 = 0;
      int $$param27 = 0;
      $$param24 = array;
      $$param25 = old26;
      $$param26 = begin;
      $$param27 = end;
      assert permutationSymb($$param24, $$param25, $$param26, $$param27);

    }

  }
    /*@
    public normal_behavior
      requires array != null && array.length < 500; 
      requires 0 <= begin && begin < end && end <= array.length; 
      ensures array.length == \old(array.length); 
      ensures (\forall int i; begin <= i < end - 1; array[i] <= array[i + 1]); 
      ensures permutation(array, \old(array), begin, end); 
      assignable array[begin .. end - 1]; 
   */

  public static void quickSort( 
  int[] array, int begin, int end) {
     
    int[] stack = new int[STACK_SIZE];
    int top = 0;
    int depth = 0;
    int depthLimit = (int)(2 * log(end - begin) / log(2)) + 3;
    stack[top++] = begin;
    stack[top++] = end;
    while (top > 0) {
      end = stack[--top];
      begin = stack[--top];
      while (end - begin > IS_THRESH && depth < depthLimit) {
        int pivot = partition(array, begin, end);
        if (pivot - begin > end - pivot) {
          stack[top++] = begin;
          stack[top++] = pivot;
          begin = pivot + 1;

        } else {
          stack[top++] = pivot + 1;
          stack[top++] = end;
          end = pivot;

        }
        depth++;

      }
      if (end - begin <= IS_THRESH || depth >= depthLimit) {
        insertionSort(array, begin, end);

      }
      depth--;

    }

  }
  
  public static void quickSortRecVerf( 
  int[] array, int begin, int end) {
    {
      CProver.assume(array != null && array.length < 500);

    }
    {
      CProver.assume(0 <= begin && begin < end && end <= array.length);

    }
    int old27 = array.length;
    int[] old28 = new int[6];
    int[] old29 = array;
    for (int i = begin; i <= end - 1; ++i) {
      for (int j = begin; j <= end - 1; ++j) {
        try {
          old28[j % 6] = array[j];

        } catch (java.lang.RuntimeException e) {

        }

      }

    }
    try {
      int[] $$param34 = null;
      int $$param35 = 0;
      int $$param36 = 0;
      int $$param37 = 0;
      int $$param38 = 0;
      int depth = 0;
      int depthLimit = (int)(2 * log(end - begin) / log(2)) + 3;
      $$param34 = array;
      $$param35 = begin;
      $$param36 = end;
      $$param37 = depth;
      $$param38 = depthLimit;
      assert !(true && (old29 != $$param34 || $$param36 - 1 > $$param36 - 1 || $$param35 < $$param35)) : "Illegal assignment to array[begin .. end - 1] conflicting with assignables array[begin .. end - 1]";
      quickSortRecImplSymb($$param34, $$param35, $$param36, $$param37, $$param38);

    } catch (BlockQuickSort.ReturnException ex) {

    }
    {
      assert array.length == old27;

    }
    {
      int quantVar81i = CProver.nondetInt();
      assert !(begin <= quantVar81i && quantVar81i < end - 1) || array[quantVar81i] <= array[quantVar81i + 1];

    }
    {
      int quantVar82i = CProver.nondetInt();
      int sum_22 = 0;
      int sum_23 = 0;
      if (!!(begin <= quantVar82i && quantVar82i < end)) {
        for (int quantVar83j = begin; begin <= quantVar83j && end - 1 >= quantVar83j; ++quantVar83j) {
          sum_22 += array[quantVar82i] == array[quantVar83j] ? 1 : 0;

        }
        for (int quantVar84j = begin; begin <= quantVar84j && end - 1 >= quantVar84j; ++quantVar84j) {
          sum_23 += array[quantVar82i] == old28[quantVar84j % 6] ? 1 : 0;

        }

      }
      assert !(begin <= quantVar82i && quantVar82i < end) || ((sum_22) == (sum_23));

    }

  }
    /*@
    public normal_behavior
      requires array != null && array.length < 500; 
      requires 0 <= begin && begin < end && end <= array.length; 
      ensures array.length == \old(array.length); 
      ensures (\forall int i; begin <= i < end - 1; array[i] <= array[i + 1]); 
      ensures (\forall int i; begin <= i < end; ((\num_of int j; begin <= j < end; array[i] == array[j]) == (\num_of int j; begin <= j < end; array[i] == \old(array[j])))); 
      assignable array[begin .. end - 1]; 
   */

  public static void quickSortRec( 
  int[] array, int begin, int end) {
    int depth = 0;
    int depthLimit = (int)(2 * log(end - begin) / log(2)) + 3;
    quickSortRecImpl(array, begin, end, depth, depthLimit);

  }
  
  public static void quickSortRecImplVerf( 
  int[] array, int begin, int end, int depth, int depthLimit) {
    {
      CProver.assume(array != null && array.length < 500);

    }
    {
      CProver.assume(0 <= begin && begin <= end && end <= array.length);

    }
    {
      CProver.assume(0 <= depth && depth <= depthLimit && depthLimit < 500);

    }
    {
      boolean b_26 = true;
      for (int quantVar85i = 0; 0 <= quantVar85i && array.length - 1 >= quantVar85i; ++quantVar85i) {
        b_26 = b_26 && (0 <= array[quantVar85i] && array[quantVar85i] <= array.length);

      }
      CProver.assume((b_26));

    }
    int old30 = array.length;
    int[] old31 = new int[6];
    int[] old32 = array;
    for (int i = begin; i <= end - 1; ++i) {
      for (int j = begin; j <= end - 1; ++j) {
        try {
          old31[j % 6] = array[j];

        } catch (java.lang.RuntimeException e) {

        }

      }

    }
    try {
      int[] $$param39 = null;
      int $$param40 = 0;
      int $$param41 = 0;
      int[] $$param42 = null;
      int $$param43 = 0;
      int $$param44 = 0;
      int[] $$param45 = null;
      int $$param46 = 0;
      int $$param47 = 0;
      int $$param48 = 0;
      int $$param49 = 0;
      int[] $$param50 = null;
      int $$param51 = 0;
      int $$param52 = 0;
      int $$param53 = 0;
      int $$param54 = 0;
      if (end - begin <= IS_THRESH || depth >= depthLimit) {
        $$param39 = array;
        $$param40 = begin;
        $$param41 = end;
        assert !(true && (old32 != $$param39 || $$param41 - 1 > $$param41 - 1 || $$param40 < $$param40)) : "Illegal assignment to array[begin .. end - 1] conflicting with assignables array[begin .. end - 1]";
        insertionSortSymb($$param39, $$param40, $$param41);
        {
          throw new BlockQuickSort.ReturnException();

        }

      }
      $$param42 = array;
      $$param43 = begin;
      $$param44 = end;
      assert !(true && (old32 != $$param42 || $$param44 - 1 > $$param44 - 1 || $$param43 < $$param43)) : "Illegal assignment to array[begin .. end - 1] conflicting with assignables array[begin .. end - 1]";
      int pivot = partitionSymb($$param42, $$param43, $$param44);
      $$param45 = array;
      $$param46 = begin;
      $$param47 = pivot;
      $$param48 = depth + 1;
      $$param49 = depthLimit;
      assert !(true && (old32 != $$param45 || $$param47 - 1 > $$param47 - 1 || $$param46 < $$param46)) : "Illegal assignment to array[begin .. end - 1] conflicting with assignables array[begin .. end - 1]";
      quickSortRecImplSymb($$param45, $$param46, $$param47, $$param48, $$param49);
      $$param50 = array;
      $$param51 = pivot;
      $$param52 = end;
      $$param53 = depth + 1;
      $$param54 = depthLimit;
      assert !(true && (old32 != $$param50 || $$param52 - 1 > $$param52 - 1 || $$param51 < $$param51)) : "Illegal assignment to array[begin .. end - 1] conflicting with assignables array[begin .. end - 1]";
      quickSortRecImplSymb($$param50, $$param51, $$param52, $$param53, $$param54);

    } catch (BlockQuickSort.ReturnException ex) {

    }
    {
      assert array.length == old30;

    }
    {
      int quantVar86i = CProver.nondetInt();
      assert !(begin <= quantVar86i && quantVar86i < end - 1) || array[quantVar86i] <= array[quantVar86i + 1];

    }
    {
      int quantVar87i = CProver.nondetInt();
      int sum_24 = 0;
      int sum_25 = 0;
      if (!!(begin <= quantVar87i && quantVar87i < end)) {
        for (int quantVar88j = begin; begin <= quantVar88j && end - 1 >= quantVar88j; ++quantVar88j) {
          sum_24 += array[quantVar87i] == array[quantVar88j] ? 1 : 0;

        }
        for (int quantVar89j = begin; begin <= quantVar89j && end - 1 >= quantVar89j; ++quantVar89j) {
          sum_25 += array[quantVar87i] == old31[quantVar89j % 6] ? 1 : 0;

        }

      }
      assert !(begin <= quantVar87i && quantVar87i < end) || ((sum_24) == (sum_25));

    }

  }
    /*@
    public normal_behavior
      requires array != null && array.length < 500; 
      requires 0 <= begin && begin <= end && end <= array.length; 
      requires 0 <= depth && depth <= depthLimit && depthLimit < 500; 
      requires (\forall int i; 0 <= i < array.length; 0 <= array[i] && array[i] <= array.length); 
      ensures array.length == \old(array.length); 
      ensures (\forall int i; begin <= i < end - 1; array[i] <= array[i + 1]); 
      ensures (\forall int i; begin <= i < end; ((\num_of int j; begin <= j < end; array[i] == array[j]) == (\num_of int j; begin <= j < end; array[i] == \old(array[j])))); 
      assignable array[begin .. end - 1]; 
   */

  public static void quickSortRecImpl( 
  int[] array, int begin, int end, int depth, int depthLimit) {
    if (end - begin <= IS_THRESH || depth >= depthLimit) {
      insertionSort(array, begin, end);
      return;

    }
    int pivot = partition(array, begin, end);
    quickSortRecImpl(array, begin, pivot, depth + 1, depthLimit);
    quickSortRecImpl(array, pivot, end, depth + 1, depthLimit);

  }
  
  public static void insertionSortVerf( 
  int[] array, int begin, int end) {
    {
      CProver.assume(array != null && array.length < 500);

    }
    {
      CProver.assume(0 <= begin && begin <= end && end <= array.length);

    }
    int old33 = array.length;
    int[] old34 = new int[6];
    int[] old35 = array;
    for (int i = begin; i <= end - 1; ++i) {
      for (int j = begin; j <= end - 1; ++j) {
        try {
          old34[j % 6] = array[j];

        } catch (java.lang.RuntimeException e) {

        }

      }

    }
    try {
      int[] $$param55 = null;
      int $$param56 = 0;
      int $$param57 = 0;
      for (int i = begin; i < end; ) {
        int j = i;
        while (j > begin && array[j - 1] > array[j]) {
          $$param55 = array;
          $$param56 = j;
          $$param57 = j - 1;
          assert !(true && (old35 != $$param55 || $$param56 > end - 1 || $$param56 < begin)) : "Illegal assignment to array[i] conflicting with assignables array[begin .. end - 1]";
          assert !(true && (old35 != $$param55 || $$param57 > end - 1 || $$param57 < begin)) : "Illegal assignment to array[j] conflicting with assignables array[begin .. end - 1]";
          swapSymb($$param55, $$param56, $$param57);
          j--;

        }
        i++;

      }

    } catch (BlockQuickSort.ReturnException ex) {

    }
    {
      assert array.length == old33;

    }
    {
      int quantVar90i = CProver.nondetInt();
      assert !(begin <= quantVar90i && quantVar90i < end - 1) || array[quantVar90i] <= array[quantVar90i + 1];

    }
    {
      int quantVar91i = CProver.nondetInt();
      int sum_26 = 0;
      int sum_27 = 0;
      if (!!(begin <= quantVar91i && quantVar91i < end)) {
        for (int quantVar92j = begin; begin <= quantVar92j && end - 1 >= quantVar92j; ++quantVar92j) {
          sum_26 += array[quantVar91i] == array[quantVar92j] ? 1 : 0;

        }
        for (int quantVar93j = begin; begin <= quantVar93j && end - 1 >= quantVar93j; ++quantVar93j) {
          sum_27 += array[quantVar91i] == old34[quantVar93j % 6] ? 1 : 0;

        }

      }
      assert !(begin <= quantVar91i && quantVar91i < end) || ((sum_26) == (sum_27));

    }

  }
    /*@
    public normal_behavior
      requires array != null && array.length < 500; 
      requires 0 <= begin && begin <= end && end <= array.length; 
      ensures array.length == \old(array.length); 
      ensures (\forall int i; begin <= i < end - 1; array[i] <= array[i + 1]); 
      ensures (\forall int i; begin <= i < end; ((\num_of int j; begin <= j < end; array[i] == array[j]) == (\num_of int j; begin <= j < end; array[i] == \old(array[j])))); 
      assignable array[begin .. end - 1]; 
   */

  public static void insertionSort( 
  int[] array, int begin, int end) {
    for (int i = begin; i < end; i++) {
      int j = i;
      while (j > begin && array[j - 1] > array[j]) {
        swap(array, j, j - 1);
        j--;

      }

    }

  }
  
  public static void swapVerf( 
  int[] array, int i, int j) {
    {
      CProver.assume(array != null && array.length < 500);

    }
    {
      CProver.assume(0 <= i && i < array.length);

    }
    {
      CProver.assume(0 <= j && j < array.length);

    }
    int old36 = array.length;
    int old37 = array[j];
    int old38 = array[i];
    try {
      int temp = array[i];
      assert !false;
      array[i] = array[j];
      assert !false;
      array[j] = temp;

    } catch (BlockQuickSort.ReturnException ex) {

    }
    {
      assert array.length == old36;

    }
    {
      {
        assert array[i] == old37;
        assert array[j] == old38;

      }

    }

  }
    /*@
    public normal_behavior
      requires array != null && array.length < 500; 
      requires 0 <= i < array.length; 
      requires 0 <= j < array.length; 
      ensures array.length == \old(array.length); 
      ensures array[i] == \old(array[j]) && array[j] == \old(array[i]); 
      assignable array[i], array[j]; 
   */

  public static void swap( 
  int[] array, int i, int j) {
    int temp = array[i];
    array[i] = array[j];
    array[j] = temp;

  }
  
  public static void sortPairVerf(int i1, int i2,  
  int[] array) {
    {
      CProver.assume(array != null && array.length < 500);

    }
    {
      CProver.assume(0 <= i1 && i1 < array.length);

    }
    {
      CProver.assume(0 <= i2 && i2 < array.length);

    }
    int old39 = array.length;
    int old40 = array[i1];
    int old41 = array[i2];
    int[] old42 = array;
    try {
      int[] $$param58 = null;
      int $$param59 = 0;
      int $$param60 = 0;
      if (array[i1] > array[i2]) {
        $$param58 = array;
        $$param59 = i1;
        $$param60 = i2;
        assert !(true && (old42 != $$param58 || $$param59 > i1 || $$param59 < i1) && ($$param58 != $$param58 || $$param59 > i2 || $$param59 < i2)) : "Illegal assignment to array[i] conflicting with assignables array[i1], array[i2]";
        assert !(true && (old42 != $$param58 || $$param60 > i1 || $$param60 < i1) && ($$param58 != $$param58 || $$param60 > i2 || $$param60 < i2)) : "Illegal assignment to array[j] conflicting with assignables array[i1], array[i2]";
        swapSymb($$param58, $$param59, $$param60);

      }

    } catch (BlockQuickSort.ReturnException ex) {

    }
    {
      assert array.length == old39;

    }
    {
      assert (old40 <= old41) ? (array[i1] == old40 && array[i2] == old41) : (array[i1] == old41 && array[i2] == old40);

    }

  }
    /*@
    public normal_behavior
      requires array != null && array.length < 500; 
      requires 0 <= i1 && i1 < array.length; 
      requires 0 <= i2 && i2 < array.length; 
      ensures array.length == \old(array.length); 
      ensures (\old(array[i1]) <= \old(array[i2])) ? (array[i1] == \old(array[i1]) && array[i2] == \old(array[i2])) : (array[i1] == \old(array[i2]) && array[i2] == \old(array[i1])); 
      assignable array[i1], array[i2]; 
   */

  public static void sortPair(int i1, int i2,  
  int[] array) {
    if (array[i1] > array[i2]) {
      swap(array, i1, i2);

    }

  }
  
  public static int medianOf3Verf( 
  int[] array, int begin, int end) {
    {
      CProver.assume(array != null && array.length < 500);

    }
    {
      CProver.assume(end - begin >= 3);

    }
    {
      CProver.assume(0 <= begin && begin < end && end <= array.length);

    }
    int old43 = array.length;
    int[] old44 = new int[6];
    int[] old45 = array;
    for (int i = begin; i <= end - 1; ++i) {
      for (int j = begin; j <= end - 1; ++j) {
        try {
          old44[j % 6] = array[j];

        } catch (java.lang.RuntimeException e) {

        }

      }

    }
    int returnVar = 0;
    try {
      int $$param61 = 0;
      int $$param62 = 0;
      int[] $$param63 = null;
      int $$param64 = 0;
      int $$param65 = 0;
      int[] $$param66 = null;
      int $$param67 = 0;
      int $$param68 = 0;
      int[] $$param69 = null;
      int mid = begin + ((end - begin) / 2);
      $$param61 = begin;
      $$param62 = mid;
      $$param63 = array;
      assert !(true && (old45 != $$param63 || $$param61 > begin || $$param61 < begin) && ($$param63 != $$param63 || $$param61 > begin + ((end - begin) / 2) || $$param61 < begin + ((end - begin) / 2)) && ($$param63 != $$param63 || $$param61 > end - 1 || $$param61 < end - 1)) : "Illegal assignment to array[i1] conflicting with assignables array[begin], array[begin + ((end - begin) / 2)], array[end - 1]";
      assert !(true && (old45 != $$param63 || $$param62 > begin || $$param62 < begin) && ($$param63 != $$param63 || $$param62 > begin + ((end - begin) / 2) || $$param62 < begin + ((end - begin) / 2)) && ($$param63 != $$param63 || $$param62 > end - 1 || $$param62 < end - 1)) : "Illegal assignment to array[i2] conflicting with assignables array[begin], array[begin + ((end - begin) / 2)], array[end - 1]";
      sortPairSymb($$param61, $$param62, $$param63);
      $$param64 = mid;
      $$param65 = end - 1;
      $$param66 = array;
      assert !(true && (old45 != $$param66 || $$param64 > begin || $$param64 < begin) && ($$param66 != $$param66 || $$param64 > begin + ((end - begin) / 2) || $$param64 < begin + ((end - begin) / 2)) && ($$param66 != $$param66 || $$param64 > end - 1 || $$param64 < end - 1)) : "Illegal assignment to array[i1] conflicting with assignables array[begin], array[begin + ((end - begin) / 2)], array[end - 1]";
      assert !(true && (old45 != $$param66 || $$param65 > begin || $$param65 < begin) && ($$param66 != $$param66 || $$param65 > begin + ((end - begin) / 2) || $$param65 < begin + ((end - begin) / 2)) && ($$param66 != $$param66 || $$param65 > end - 1 || $$param65 < end - 1)) : "Illegal assignment to array[i2] conflicting with assignables array[begin], array[begin + ((end - begin) / 2)], array[end - 1]";
      sortPairSymb($$param64, $$param65, $$param66);
      $$param67 = begin;
      $$param68 = mid;
      $$param69 = array;
      assert !(true && (old45 != $$param69 || $$param67 > begin || $$param67 < begin) && ($$param69 != $$param69 || $$param67 > begin + ((end - begin) / 2) || $$param67 < begin + ((end - begin) / 2)) && ($$param69 != $$param69 || $$param67 > end - 1 || $$param67 < end - 1)) : "Illegal assignment to array[i1] conflicting with assignables array[begin], array[begin + ((end - begin) / 2)], array[end - 1]";
      assert !(true && (old45 != $$param69 || $$param68 > begin || $$param68 < begin) && ($$param69 != $$param69 || $$param68 > begin + ((end - begin) / 2) || $$param68 < begin + ((end - begin) / 2)) && ($$param69 != $$param69 || $$param68 > end - 1 || $$param68 < end - 1)) : "Illegal assignment to array[i2] conflicting with assignables array[begin], array[begin + ((end - begin) / 2)], array[end - 1]";
      sortPairSymb($$param67, $$param68, $$param69);
      {
        returnVar = mid;
        throw new BlockQuickSort.ReturnException();

      }

    } catch (BlockQuickSort.ReturnException ex) {

    }
    {
      assert array.length == old43;

    }
    {
      assert returnVar == begin + ((end - begin) / 2);

    }
    {
      {
        assert array[begin] <= array[returnVar];
        assert array[returnVar] <= array[end - 1];

      }

    }
    {
      int quantVar94i = CProver.nondetInt();
      int sum_28 = 0;
      int sum_29 = 0;
      if (!!(begin <= quantVar94i && quantVar94i < end)) {
        for (int quantVar95j = begin; begin <= quantVar95j && end - 1 >= quantVar95j; ++quantVar95j) {
          sum_28 += array[quantVar94i] == array[quantVar95j] ? 1 : 0;

        }
        for (int quantVar96j = begin; begin <= quantVar96j && end - 1 >= quantVar96j; ++quantVar96j) {
          sum_29 += array[quantVar94i] == old44[quantVar96j % 6] ? 1 : 0;

        }

      }
      assert !(begin <= quantVar94i && quantVar94i < end) || ((sum_28) == (sum_29));

    }
    return returnVar;

  }
    /*@
    public normal_behavior
      requires array != null && array.length < 500; 
      requires end - begin >= 3; 
      requires 0 <= begin && begin < end && end <= array.length; 
      ensures array.length == \old(array.length); 
      ensures \result == begin + ((end - begin) / 2); 
      ensures array[begin] <= array[\result] && array[\result] <= array[end - 1]; 
      ensures (\forall int i; begin <= i < end; ((\num_of int j; begin <= j < end; array[i] == array[j]) == (\num_of int j; begin <= j < end; array[i] == \old(array[j])))); 
      assignable array[begin], array[begin + ((end - begin) / 2)], array[end - 1]; 
   */

  public static int medianOf3( 
  int[] array, int begin, int end) {
    int mid = begin + ((end - begin) / 2);
    sortPair(begin, mid, array);
    sortPair(mid, end - 1, array);
    sortPair(begin, mid, array);
    return mid;

  }
  
  public static int partitionVerf( 
  int[] array, int begin, int end) {
    {
      CProver.assume(array != null && array.length < 500);

    }
    {
      CProver.assume(end - begin >= 3);

    }
    {
      CProver.assume(0 <= begin && begin < end && end <= array.length);

    }
    int old46 = array.length;
    int[] old47 = new int[6];
    int[] old48 = array;
    for (int i = begin; i <= end - 1; ++i) {
      for (int j = begin; j <= end - 1; ++j) {
        try {
          old47[j % 6] = array[j];

        } catch (java.lang.RuntimeException e) {

        }

      }

    }
    int returnVar = 0;
    try {
      int[] $$param70 = null;
      int $$param71 = 0;
      int $$param72 = 0;
      int[] $$param73 = null;
      int $$param74 = 0;
      int $$param75 = 0;
      int $$param76 = 0;
      $$param70 = array;
      $$param71 = begin;
      $$param72 = end;
      assert !(true && (old48 != $$param70 || $$param71 > $$param72 - 1 || $$param71 < $$param71)) : "Illegal assignment to array[begin] conflicting with assignables array[begin .. end - 1]";
      assert !(true && (old48 != $$param70 || $$param71 + (($$param72 - $$param71) / 2) > $$param72 - 1 || $$param71 + (($$param72 - $$param71) / 2) < $$param71)) : "Illegal assignment to array[begin + ((end - begin) / 2)] conflicting with assignables array[begin .. end - 1]";
      assert !(true && (old48 != $$param70 || $$param72 - 1 > $$param72 - 1 || $$param72 - 1 < $$param71)) : "Illegal assignment to array[end - 1] conflicting with assignables array[begin .. end - 1]";
      int mid = medianOf3Symb($$param70, $$param71, $$param72);
      $$param73 = array;
      $$param74 = begin + 1;
      $$param75 = end - 1;
      $$param76 = mid;
      assert !(true && (old48 != $$param73 || $$param75 - 1 > end - 1 || $$param74 < begin)) : "Illegal assignment to array[originalBegin .. originalEnd - 1] conflicting with assignables array[begin .. end - 1]";
      {
        returnVar = hoareBlockPartitionSymb($$param73, $$param74, $$param75, $$param76);
        throw new BlockQuickSort.ReturnException();

      }

    } catch (BlockQuickSort.ReturnException ex) {

    }
    {
      assert array.length == old46;

    }
    {
      {
        assert begin <= returnVar;
        assert returnVar < end;

      }

    }
    {
      int quantVar97i = CProver.nondetInt();
      assert !(begin <= quantVar97i && quantVar97i <= returnVar) || array[quantVar97i] <= array[returnVar];

    }
    {
      int quantVar98i = CProver.nondetInt();
      assert !(returnVar <= quantVar98i && quantVar98i < end) || array[returnVar] <= array[quantVar98i];

    }
    {
      int quantVar99i = CProver.nondetInt();
      int sum_30 = 0;
      int sum_31 = 0;
      if (!!(begin <= quantVar99i && quantVar99i < end)) {
        for (int quantVar100j = begin; begin <= quantVar100j && end - 1 >= quantVar100j; ++quantVar100j) {
          sum_30 += array[quantVar99i] == array[quantVar100j] ? 1 : 0;

        }
        for (int quantVar101j = begin; begin <= quantVar101j && end - 1 >= quantVar101j; ++quantVar101j) {
          sum_31 += array[quantVar99i] == old47[quantVar101j % 6] ? 1 : 0;

        }

      }
      assert !(begin <= quantVar99i && quantVar99i < end) || ((sum_30) == (sum_31));

    }
    return returnVar;

  }
    /*@
    public normal_behavior
      requires array != null && array.length < 500; 
      requires end - begin >= 3; 
      requires 0 <= begin && begin < end && end <= array.length; 
      ensures array.length == \old(array.length); 
      ensures begin <= \result && \result < end; 
      ensures (\forall int i; begin <= i <= \result; array[i] <= array[\result]); 
      ensures (\forall int i; \result <= i < end; array[\result] <= array[i]); 
      ensures (\forall int i; begin <= i < end; ((\num_of int j; begin <= j < end; array[i] == array[j]) == (\num_of int j; begin <= j < end; array[i] == \old(array[j])))); 
      assignable array[begin .. end - 1]; 
   */

  public static int partition( 
  int[] array, int begin, int end) {
    int mid = medianOf3(array, begin, end);
    return hoareBlockPartition(array, begin + 1, end - 1, mid);

  }
  
  public static double logVerf(double a) {
    double returnVar = 0.0;
    try {
      if (a <= 0) {
        throw new IllegalArgumentException("Argument must be positive.");

      }
      int iterations = 1000;
      double result = 0.0;
      double x = (a - 1) / (a + 1);
      for (int i = 0; i < iterations; ) {
        int exponent = 2 * i + 1;
        result += power(x, exponent) / exponent;
        i++;

      }
      {
        returnVar = 2 * result;
        throw new BlockQuickSort.ReturnException();

      }

    } catch (BlockQuickSort.ReturnException ex) {

    } catch (java.lang.RuntimeException e) {
      CProver.assume(false);

    }
    return returnVar;

  }
    /*@
    public behavior
      signals_only java.lang.RuntimeException; 
   */

  public static double log(double a) {
    if (a <= 0) {
      throw new IllegalArgumentException("Argument must be positive.");

    }
    int iterations = 1000;
    double result = 0.0;
    double x = (a - 1) / (a + 1);
    for (int i = 0; i < iterations; i++) {
      int exponent = 2 * i + 1;
      result += power(x, exponent) / exponent;

    }
    return 2 * result;

  }
  
  private static double powerVerf(double base, int exponent) {
    double returnVar = 0.0;
    try {
      double result = 1.0;
      for (int i = 0; i < exponent; ) {
        result *= base;
        i++;

      }
      {
        returnVar = result;
        throw new BlockQuickSort.ReturnException();

      }

    } catch (BlockQuickSort.ReturnException ex) {

    } catch (java.lang.RuntimeException e) {
      CProver.assume(false);

    }
    return returnVar;

  }
    /*@
    private behavior
      signals_only java.lang.RuntimeException; 
   */

  private static double power(double base, int exponent) {
    double result = 1.0;
    for (int i = 0; i < exponent; i++) {
      result *= base;

    }
    return result;

  }
  
   
  public static boolean permutationVerf( 
  int[] array1,  
  int[] array2, int begin, int end) {
    {
      CProver.assume(array1 != null);

    }
    {
      CProver.assume(array2 != null);

    }
    {
      CProver.assume(0 <= begin && begin <= end && end <= array1.length);

    }
    {
      CProver.assume(array1.length == array2.length);

    }
    int old49 = array1.length;
    int old50 = array2.length;
    boolean returnVar = true;
    try {
      {
        int i = begin;
        {
          int quantVar108j = CProver.nondetInt();
          int sum_36 = 0;
          int sum_37 = 0;
          {
            assert begin <= i;
            assert i <= end;

          }
          if (!!(begin <= quantVar108j && quantVar108j < i)) {
            for (int quantVar109k = begin; begin <= quantVar109k && end - 1 >= quantVar109k; ++quantVar109k) {
              sum_36 += array1[quantVar108j] == array1[quantVar109k] ? 1 : 0;

            }
            for (int quantVar110k = begin; begin <= quantVar110k && end - 1 >= quantVar110k; ++quantVar110k) {
              sum_37 += array1[quantVar108j] == array2[quantVar110k] ? 1 : 0;

            }

          }
          assert !(begin <= quantVar108j && quantVar108j < i) || (sum_36) == (sum_37);

        }
        i = CProver.nondetInt();
        int oldDecreasesClauseValue1 = end - i;
        {
          int sum_38 = 0;
          int sum_39 = 0;
          boolean b_28 = true;
          CProver.assume(begin <= i && i <= end);
          for (int quantVar111j = begin; begin <= quantVar111j && i - 1 >= quantVar111j; ++quantVar111j) {
            for (int quantVar112k = begin; begin <= quantVar112k && end - 1 >= quantVar112k; ++quantVar112k) {
              sum_38 += array1[quantVar111j] == array1[quantVar112k] ? 1 : 0;

            }
            for (int quantVar113k = begin; begin <= quantVar113k && end - 1 >= quantVar113k; ++quantVar113k) {
              sum_39 += array1[quantVar111j] == array2[quantVar113k] ? 1 : 0;

            }
            b_28 = b_28 && (sum_38) == (sum_39);

          }
          CProver.assume((b_28));

        }
        if (i < end) {
          int count1 = 0;
          int count2 = 0;
          {
            int j = begin;
            {
              int sum_40 = 0;
              int sum_41 = 0;
              {
                assert begin <= j;
                assert j <= end;

              }
              for (int quantVar114k = begin; begin <= quantVar114k && j - 1 >= quantVar114k; ++quantVar114k) {
                sum_40 += array1[i] == array1[quantVar114k] ? 1 : 0;

              }
              assert count1 == (sum_40);
              for (int quantVar115k = begin; begin <= quantVar115k && j - 1 >= quantVar115k; ++quantVar115k) {
                sum_41 += array1[i] == array2[quantVar115k] ? 1 : 0;

              }
              assert count2 == (sum_41);

            }
            j = CProver.nondetInt();
            count2 = CProver.nondetInt();
            count1 = CProver.nondetInt();
            int oldDecreasesClauseValue2 = end - j;
            {
              int sum_42 = 0;
              int sum_43 = 0;
              CProver.assume(begin <= j && j <= end);
              for (int quantVar116k = begin; begin <= quantVar116k && j - 1 >= quantVar116k; ++quantVar116k) {
                sum_42 += array1[i] == array1[quantVar116k] ? 1 : 0;

              }
              CProver.assume(count1 == (sum_42));
              for (int quantVar117k = begin; begin <= quantVar117k && j - 1 >= quantVar117k; ++quantVar117k) {
                sum_43 += array1[i] == array2[quantVar117k] ? 1 : 0;

              }
              CProver.assume(count2 == (sum_43));

            }
            if (j < end) {
              if (array1[i] == array1[j]) {
                count1++;

              }
              if (array1[i] == array2[j]) {
                count2++;

              }
              j++;
              {
                int sum_44 = 0;
                int sum_45 = 0;
                {
                  assert begin <= j;
                  assert j <= end;

                }
                for (int quantVar118k = begin; begin <= quantVar118k && j - 1 >= quantVar118k; ++quantVar118k) {
                  sum_44 += array1[i] == array1[quantVar118k] ? 1 : 0;

                }
                assert count1 == (sum_44);
                for (int quantVar119k = begin; begin <= quantVar119k && j - 1 >= quantVar119k; ++quantVar119k) {
                  sum_45 += array1[i] == array2[quantVar119k] ? 1 : 0;

                }
                assert count2 == (sum_45);

              }
              {
                assert end - j >= 0;
                assert end - j < oldDecreasesClauseValue2;

              }
              CProver.assume(false);

            }

          }
          if (count1 != count2) {
            {
              returnVar = false;
              throw new BlockQuickSort.ReturnException();

            }

          }
          i++;
          {
            int quantVar120j = CProver.nondetInt();
            int sum_46 = 0;
            int sum_47 = 0;
            {
              assert begin <= i;
              assert i <= end;

            }
            if (!!(begin <= quantVar120j && quantVar120j < i)) {
              for (int quantVar121k = begin; begin <= quantVar121k && end - 1 >= quantVar121k; ++quantVar121k) {
                sum_46 += array1[quantVar120j] == array1[quantVar121k] ? 1 : 0;

              }
              for (int quantVar122k = begin; begin <= quantVar122k && end - 1 >= quantVar122k; ++quantVar122k) {
                sum_47 += array1[quantVar120j] == array2[quantVar122k] ? 1 : 0;

              }

            }
            assert !(begin <= quantVar120j && quantVar120j < i) || (sum_46) == (sum_47);

          }
          {
            assert end - i >= 0;
            assert end - i < oldDecreasesClauseValue1;

          }
          CProver.assume(false);

        }

      }
      {
        returnVar = true;
        throw new BlockQuickSort.ReturnException();

      }

    } catch (BlockQuickSort.ReturnException ex) {

    }
    {
      assert array1.length == old49;

    }
    {
      assert array2.length == old50;

    }
    {
      int quantVar102i = CProver.nondetInt();
      int sum_32 = 0;
      int sum_33 = 0;
      int sum_34 = 0;
      int sum_35 = 0;
      boolean b_27 = false;
      if (!!returnVar) {
        if (!!(begin <= quantVar102i && quantVar102i < end)) {
          for (int quantVar103j = begin; begin <= quantVar103j && end - 1 >= quantVar103j; ++quantVar103j) {
            sum_32 += array1[quantVar102i] == array1[quantVar103j] ? 1 : 0;

          }
          for (int quantVar104j = begin; begin <= quantVar104j && end - 1 >= quantVar104j; ++quantVar104j) {
            sum_33 += array1[quantVar102i] == array2[quantVar104j] ? 1 : 0;

          }

        }

      }
      if (!returnVar || (!(begin <= quantVar102i && quantVar102i < end) || ((sum_32) == (sum_33)))) {
        for (int quantVar105i = begin; begin <= quantVar105i && end - 1 >= quantVar105i; ++quantVar105i) {
          for (int quantVar106j = begin; begin <= quantVar106j && end - 1 >= quantVar106j; ++quantVar106j) {
            sum_34 += array1[quantVar105i] == array1[quantVar106j] ? 1 : 0;

          }
          for (int quantVar107j = begin; begin <= quantVar107j && end - 1 >= quantVar107j; ++quantVar107j) {
            sum_35 += array1[quantVar105i] == array2[quantVar107j] ? 1 : 0;

          }
          b_27 = b_27 || !((sum_34) == (sum_35));

        }

      }
      {
        assert !returnVar || (!(begin <= quantVar102i && quantVar102i < end) || ((sum_32) == (sum_33)));
        assert b_27 || returnVar;

      }

    }
    return returnVar;

  }
    /*@
    public normal_behavior
      requires array1 != null; 
      requires array2 != null; 
      requires 0 <= begin && begin <= end && end <= array1.length; 
      requires array1.length == array2.length; 
      ensures array1.length == \old(array1.length); 
      ensures array2.length == \old(array2.length); 
      ensures \result == (\forall int i; begin <= i < end; ((\num_of int j; begin <= j < end; array1[i] == array1[j]) == (\num_of int j; begin <= j < end; array1[i] == array2[j]))); 
   */

   
  public static boolean permutation( 
  int[] array1,  
  int[] array2, int begin, int end) {
    //@ loop_invariant begin <= i <= end;
    //@ loop_invariant (\forall int j; begin <= j < i; (\num_of int k; begin <= k < end; array1[j] == array1[k]) == (\num_of int k; begin <= k < end; array1[j] == array2[k]));
    //@ loop_modifies i;
    //@ loop_decreases end - i;
    for (int i = begin; i < end; i++) {
      int count1 = 0;
      int count2 = 0;
      //@ loop_invariant begin <= j <= end;
      //@ loop_invariant count1 == (\num_of int k; begin <= k < j; array1[i] == array1[k]);
      //@ loop_invariant count2 == (\num_of int k; begin <= k < j; array1[i] == array2[k]);
      //@ loop_modifies j, count1, count2;
      //@ loop_decreases end - j;
      for (int j = begin; j < end; j++) {
        if (array1[i] == array1[j]) {
          count1++;

        }
        if (array1[i] == array2[j]) {
          count2++;

        }
        j++;

      }
      if (count1 != count2) {
        return false;

      }
      i++;

    }
    return true;

  }
  
  public static class ReturnException extends java.lang.RuntimeException {
  }
}