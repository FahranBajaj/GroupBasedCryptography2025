LoadPackage("AutomGrp", true);
Reset(GlobalMersenneTwister,CurrentDateTimeString()); #new random seed

FastFiniteState := function(group)
    local finiteState, finite;

    finite := IO_CallWithTimeout(rec(seconds := 10), IsFinite, group);
    if (finite[1] = true and finite[2] = false) or (finite[1] = false) then   
        finiteState := IO_CallWithTimeout(rec(seconds := 10), IsFiniteState, group);
        return finiteState[1] = true;
    fi;
    return false;
end;

OnBreak := function()
    QuitGap();
end;

RandomElement := function()
    local wordLength, word, i;
    wordLength := Random([1..10]);
    word := [];
    for i in [1..wordLength] do 
        Append(word, [Random([1, 2, -1, -2])]);
    od;
    return word;
end;

ConjugateLists := function(elem, conjugator)
    local word, i;
    word := [];
    for i in Reversed(conjugator) do 
        Append(word, [-1*i]);
    od;
    Append(word, elem);
    Append(word, conjugator);
    return word;
end;

# i := 1;
# while true do 
#     conj123 := RandomElement();
#     conj4 := RandomElement();
#     conj5 := RandomElement();
#     numGenerators := Random([2..5]);
#     perms := List([1..numGenerators], i -> Random(SymmetricGroup(3)));
#     if Group(perms) = Center(Group(perms)) then 
#         continue;
#     fi;
#     centers := List([1..numGenerators], i -> RandomElement());
#     G := SelfSimilarGroup(List([1..numGenerators], i -> Concatenation(
#         List([1..3], j -> ConjugateLists(centers[i], conj123)),
#         [ConjugateLists(centers[i], conj4) , ConjugateLists(centers[i], conj5),  
#         perms[i]]
#     )), true);
#     if FastFiniteState(G) then 
#         break;
#     fi;
#     Print(i, "\n");
#     i := i + 1;
# od;

PermActionAtVertex := function(perm, bigLevel, vertex)
    local topLevelAction, permSplitLeftRight, topLevelSwap, singleSubtreePerm, permAsList, i, nextVertex;

    topLevelAction := PermActionOnLevel(perm, bigLevel, 1, 2);
    if vertex = [] then 
        return topLevelAction;
    fi;
    if topLevelAction = () then 
        permSplitLeftRight := perm;
    else 
        topLevelSwap := PermList(Concatenation([2^(bigLevel - 1) + 1..2^bigLevel], [1..2^(bigLevel-1)]));
        permSplitLeftRight := perm * topLevelSwap;
    fi;
    if vertex[1] = 1 then 
        singleSubtreePerm := RestrictedPermNC(permSplitLeftRight, [1..2^(bigLevel - 1)]);
    else 
        singleSubtreePerm := PermList(List([2^(bigLevel - 1) + 1..2^bigLevel], i -> i^permSplitLeftRight - 2^(bigLevel - 1)));
    fi;

    nextVertex := ShallowCopy(vertex);
    Remove(nextVertex, 1);
    return PermActionAtVertex(singleSubtreePerm, bigLevel - 1, nextVertex);
end;

PermActionBelowVertex := function(perm, bigLevel, vertex)
    local topLevelAction, permSplitLeftRight, topLevelSwap, singleSubtreePerm, permAsList, i, nextVertex;

    if vertex = [] then 
        return perm;
    fi;
    topLevelAction := PermActionOnLevel(perm, bigLevel, 1, 2);
    if topLevelAction = () then 
        permSplitLeftRight := perm;
    else 
        topLevelSwap := PermList(Concatenation([2^(bigLevel - 1) + 1..2^bigLevel], [1..2^(bigLevel-1)]));
        permSplitLeftRight := perm * topLevelSwap;
    fi;
    if vertex[1] = 1 then 
        singleSubtreePerm := RestrictedPermNC(permSplitLeftRight, [1..2^(bigLevel - 1)]);
    else 
        singleSubtreePerm := PermList(List([2^(bigLevel - 1) + 1..2^bigLevel], i -> i^permSplitLeftRight - 2^(bigLevel - 1)));
    fi;

    nextVertex := ShallowCopy(vertex);
    Remove(nextVertex, 1);
    return PermActionBelowVertex(singleSubtreePerm, bigLevel - 1, nextVertex);
end;

PortraitToPermutation := function(portrait, depth_of_portrait)
    local N_LETTERS, i, perms, l;
    N_LETTERS := 2;

    if Length(portrait) = 1 then
        return portrait[1];
    fi;

    perms:=List([1..N_LETTERS],x->PortraitToPermutation (portrait[x+1], depth_of_portrait-1));

    l := [];

    for i in [1..N_LETTERS] 
        do
            Append(l, List(ListPerm(perms[i],N_LETTERS^(depth_of_portrait-1)),x->x+N_LETTERS^(depth_of_portrait-1)*(i^portrait[1]-1)));
        od;

    return PermList(l);
end;

PortraitWithPermAtVertex := function(perm, vertex, level)
    local nextVertex;
    if level = 1 then
        return [perm];
    fi;
    if vertex = [] then 
        return [perm, PortraitWithPermAtVertex((), [], level - 1), PortraitWithPermAtVertex((), [], level - 1)];
    fi;
    nextVertex := ShallowCopy(vertex);
    Remove(nextVertex, 1);
    if vertex[1] = 1 then 
        return [(), PortraitWithPermAtVertex(perm, nextVertex, level - 1), PortraitWithPermAtVertex((), [], level - 1)];
    else 
        return [(), PortraitWithPermAtVertex((), [], level - 1), PortraitWithPermAtVertex(perm, nextVertex, level - 1)];
    fi;
end;

CompletePermGroupOnLevel := function(level)
    local perms, current_level, node;
    perms := [];
    for current_level in [0..level - 1] do 
        for node in [1..2^current_level] do 
            Append(perms, [PortraitToPermutation(PortraitWithPermAtVertex((1, 2), VertexNumber(node, current_level, 2), level), level)]);
        od;
    od;
    return Group(perms);
end;

LEVEL := 3;
G := CompletePermGroupOnLevel(LEVEL);
AllowablePerm := function(perm, level)
    local section1Perm, section2Perm;
    if level = 1 then 
        return true;
    fi;
    section1Perm := PermActionBelowVertex(perm, level, [1]);
    section2Perm := PermActionBelowVertex(perm, level, [2]);

    if PermActionAtVertex(perm, level, []) = () then 
        #acts trivially, must check if sections are conjugate
        if not IsConjugate(G, section1Perm, section2Perm) then 
            return false;
        fi;
    fi;

    #must check if sections are also allowable
    #(groups are self-similar so sections are also group elements that must be allowable)
    return AllowablePerm(section1Perm, level - 1) and AllowablePerm(section2Perm, level - 1);
end;

AllowablePermCombo := function(perm, level, perm1, perm2)
    local section1Perm, section2Perm;
    if level = 1 then 
        return true;
    fi;
    section1Perm := PermActionBelowVertex(perm, level, [1]);
    section2Perm := PermActionBelowVertex(perm, level, [2]);

    if PermActionAtVertex(perm, level, []) = () then 
        #acts trivially, must check if sections are conjugate
        if not IsConjugate(Group([PermActionOnLevel(perm1, LEVEL, level - 1, 2), PermActionOnLevel(perm2, LEVEL, level - 1, 2)]), section1Perm, section2Perm) then 
            return false;
        fi;
    fi;

    #must check if sections are also allowable
    #(groups are self-similar so sections are also group elements that must be allowable)
    return AllowablePermCombo(section1Perm, level - 1, perm1, perm2) and AllowablePermCombo(section2Perm, level - 1, perm1, perm2);
end;

allowablePermsInGroup := [];
for elem in G do 
    if AllowablePerm(elem, LEVEL) then 
        Append(allowablePermsInGroup, [elem]);
    fi;
od;
Sort(allowablePermsInGroup);

nonCommutingPairs := [];

for perm1 in allowablePermsInGroup do 
    permsCopy := ShallowCopy(allowablePermsInGroup);
    SubtractSet(permsCopy, Elements(Centralizer(G, perm1)));
    for perm2 in permsCopy do 
        if AllowablePermCombo(perm1*perm2, LEVEL, perm1, perm2) and AllowablePermCombo(perm2*perm1, LEVEL, perm1, perm2) then 
            Append(nonCommutingPairs, [[perm1, perm2]]);
        fi;
    od;
od;

