
# identify A4 generators from PSL27 elements.
# The A4 generators are s and t fulfill
# s^2=t^3=(st)^3=e.
IdentifyA4FromPSL27:=function(first)
    local G, GFp, slist, t, a, b, elist, i, res, hom;
    
    G := PSL(2,7);
    # we identify t to generator b of PSL27.
    if first then
        b := First(GeneratorsOfGroup(G), x-> Order(x) = 3);
    else
        b := Filtered(GeneratorsOfGroup(G), x-> Order(x) = 3)[2];
    fi;
    t := b;

    # find generator a of PSL27.
    elist := Elements(G);
    a := First(elist, x-> Order(x) = 2 and Order(x*b)=7 and Order(x*b*x^-1*b^-1) = 4);

    # now we need to find s.
    slist := Filtered(elist, x-> Order(x) = 2 and Order(x*t) = 3);
    
    # find relationship between a and s.
    GFp := GroupByGenerators([a, b]);
    res := [];
    hom := EpimorphismFromFreeGroup(GFp:names:=["a","b"]);

    for i in [1..Length(slist)] do
        Add(res, [PreImagesRepresentative(hom, slist[i]), PreImagesRepresentative(hom, t)]);
    od;

    return res;
end;

# identify A4 generators from S4 elements.
# The A4 generators are s and t fulfill
# s^2=t^3=(st)^3=e.
# S4 generators are: a^4=b^2=(ab)^3=e.
IdentifyA4FromS4:=function()
    local G, a, b, s, elist, tlist, i, hom, GFp, res;
    G := SymmetricGroup(4);
    a := First(GeneratorsOfGroup(G), x -> Order(x) = 4);
    b := First(GeneratorsOfGroup(G), x -> Order(x) = 2);

    # identify s = a^2;
    s := a^2;

    # find all possible t.    
    elist := Elements(G);
    tlist := Filtered(elist, x -> Order(x) = 3 and Order(s*x) = 3);
    
    # find relationship between t and a, b.
    GFp := GroupByGenerators([a, b]);
    res := [];
    hom := EpimorphismFromFreeGroup(GFp:names:=["a","b"]);
    
    for i in [1..Length(tlist)] do
        Add(res, [PreImagesRepresentative(hom, s), PreImagesRepresentative(hom, tlist[i])]);
    od;

    return res;
end;

# identify S4 generators from PSL(2,7) generators.
# PSL(2,7): A^2=B^3=(AB)^7=[A,B]^4=e
# S4: a^4=b^2=(ab)^3=e
# possible try is that let b=A
IdentifyS4FromPSL27A:=function(first)
    local G, GFp, alist, A, B, a, b, elist, i, res, hom;
    
    G := PSL(2,7);
    elist := Elements(G);
    # first find A, B of PSL27
    if first then
        B := First(GeneratorsOfGroup(G), x-> Order(x) = 3);
    else
        B := Filtered(GeneratorsOfGroup(G), x-> Order(x) = 3)[2];
    fi;

    # find generator A of PSL27.    
    A := First(elist, x-> Order(x) = 2 and Order(x*B)=7 and Order(x*B*x^-1*B^-1) = 4);

    # Identify b to A
    b := A;
    # now we need to find a.
    alist := Filtered(elist, x-> Order(x) = 4 and Order(x*b) = 3);
    
    # find relationship between a and s.
    GFp := GroupByGenerators([A, B]);
    res := [];
    hom := EpimorphismFromFreeGroup(GFp:names:=["A","B"]);

    for i in [1..Length(alist)] do
        Add(res, [PreImagesRepresentative(hom, alist[i]), PreImagesRepresentative(hom, b)]);
    od;

    return res;
end;

# identify S4 generators from PSL(2,7) generators.
# PSL(2,7): A^2=B^3=(AB)^7=[A,B]^4=e
# S4: a^4=b^2=(ab)^3=e
# second try: let ab=B
IdentifyS4FromPSL27B:=function(first)
    local G, GFp, alist, A, B, a, ab, b, elist, i, res, hom;
    
    G := PSL(2,7);
    elist := Elements(G);
    # first find A, B of PSL27
    if first then
        B := First(GeneratorsOfGroup(G), x-> Order(x) = 3);
    else
        B := Filtered(GeneratorsOfGroup(G), x-> Order(x) = 3)[2];
    fi;

    # find generator A of PSL27.    
    A := First(elist, x-> Order(x) = 2 and Order(x*B)=7 and Order(x*B*x^-1*B^-1) = 4);

    # Identify ab to B
    ab := B;
    # now we need to find a.
    alist := Filtered(elist, x-> Order(x) = 4 and Order(x^-1*ab) = 2);
    
    # find relationship between a and s.
    GFp := GroupByGenerators([A, B]);
    res := [];
    hom := EpimorphismFromFreeGroup(GFp:names:=["A","B"]);

    for i in [1..Length(alist)] do
        b := alist[i]^-1*ab;
        Add(res, [PreImagesRepresentative(hom, alist[i]), PreImagesRepresentative(hom, b)]);
    od;

    return res;
end;

# identify S4 generators from PSL(2,7) generators.
# PSL(2,7): A^2=B^3=(AB)^7=[A,B]^4=e
# S4: a^4=b^2=(ab)^3=e
# third try: let a=[A,B]
IdentifyS4FromPSL27C:=function(first)
    local G, GFp, blist, ablist, A, B, a, b, elist, i, res, hom;
    
    G := PSL(2,7);
    elist := Elements(G);
    # first find A, B of PSL27
    if first then
        B := First(GeneratorsOfGroup(G), x-> Order(x) = 3);
    else
        B := Filtered(GeneratorsOfGroup(G), x-> Order(x) = 3)[2];
    fi;

    # find generator A of PSL27.    
    A := First(elist, x-> Order(x) = 2 and Order(x*B)=7 and Order(x*B*x^-1*B^-1) = 4);

    # Identify a to [A,B]
    a := A*B*A^-1*B^-1;
    # now we need to find b or ab.
    blist := Filtered(elist, x-> Order(x) = 2 and Order(a*x) = 3);
    ablist := Filtered(elist, x-> Order(x)=3 and Order(a^-1*x)=2);
    
    # find relationship between generators.
    GFp := GroupByGenerators([A, B]);
    res := [];
    hom := EpimorphismFromFreeGroup(GFp:names:=["A","B"]);
    Print("a=[A,B]\n");

    for i in [1..Length(blist)] do
        Add(res, ["b", PreImagesRepresentative(hom, blist[i])]);
    od;

    for i in [1..Length(ablist)] do
        Add(res, ["ab", PreImagesRepresentative(hom, ablist[i])]);
    od;

    return res;
end;
