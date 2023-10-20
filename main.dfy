class {:autocontracts} Conjunto
{
    //Implementação
    var arr: array<int>
    var index: nat

    //Abstração
    ghost var list: seq<int>
    ghost var size: nat

    constructor()
    ensures arr.Length == 10
    ensures index == 0
    ensures list == []
    ensures Valid()
    {
        arr := new int[10];
        index := 0;
        list := [];
        size := 0;
    }

    //Invariante de classe
    ghost predicate Valid()
    {
        index <= arr.Length &&
        list == arr[0..index] &&
        index == |list|
    }

    method Add(x: int) returns (r: bool)
    requires Valid()
    ensures Valid() && x in list
    {
        r := this.Contains(x);
        if (!r)
        {
            arr[index] := x;
            index := index + 1;
            list := list + [x];
        }
        if (index == arr.Length) 
        {
            var temp := new int[index * 2];
            var i := 0;
            while (i < index)
            invariant 0 <= i <= index
            invariant index == arr.Length
            invariant arr.Length < temp.Length
            decreases index - i
            {
                temp[i] := arr[i];
                i := i + 1;
            }
            arr := temp;
            assert index < arr.Length;
        }
        assert index < arr.Length;
        assert arr.Length >= old(arr.Length);
    }

    /* method Add(x: int) returns (r: bool)
    requires Valid()
    /* ensures r == true ==> arr[index] == x
    ensures r == true ==> list == old(list) + [x]
    ensures r == true ==> index == old(index) + 1
    ensures r == false ==> list == old(list)
    ensures r == false ==> index == old(index) */
    ensures Valid()
    {
        var contains := this.Contains(x);
        r := !contains;
        if (!contains)
        {
            arr[index] := x;
            index := index + 1;
            list := list + [x];

            assert list == old(list) + [x];
            assert index == old(index) + 1;

            if (index == arr.Length) 
            {
                var temp := new int[index * 2];
                var i := 0;
                while (i < index)
                invariant 0 <= i <= index
                invariant index == arr.Length
                invariant arr.Length < temp.Length
                decreases index - i
                {
                    temp[i] := arr[i];
                    i := i + 1;
                }
                arr := temp;
                assert index < arr.Length;
                assert arr.Length > old(arr.Length);
            }
        }
        if (!r)
        {
            assert list == old(list);
            assert index == old(index);
        }
        assert index < arr.Length;
        assert arr.Length >= old(arr.Length);
    } */

    method Remove(x: int) returns (r: bool)
    requires Valid()
    ensures r == false ==> x !in list
    {
        r := this.Contains(x);
        if (r)
        {
            var i := 0;
            while (i < index && arr[i] != x)
            invariant 0 <= i <= index
            invariant forall k :: 0 <= k < i ==> arr[k] != x
            decreases index - i
            {
                i := i + 1;
            }
            assert arr[i] == x;
            list := list[..i] + list[i+1..];
            i := i + 1;
        }
    } 

    method IsEmpty() returns (r: bool)
    requires Valid()
    ensures r == true ==> |list| == 0
    ensures r == false ==> |list| > 0
    {
        r := index == 0;
    }

    method Size() returns (r: nat)
    requires Valid()
    ensures r == |list|
    {
        r := index;
    }

    method Contains(x: int) returns (r: bool)
    requires Valid()
    ensures r == false ==> forall k :: 0 <= k < index ==> arr[k] != x
    ensures r == false ==> x !in list
    ensures r == true ==> x in list
    {
        var i := 0;
        while (i < index)
        invariant 0 <= i <= index
        invariant forall k :: 0 <= k < i ==> arr[k] != x
        decreases index - i
        {
            if (arr[i] == x)
            {
                return true;
            }
            i := i + 1;
        }
        return false;
    }
}
