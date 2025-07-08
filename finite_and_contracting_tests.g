
TestRandomGroup := function(degree, num_gens, p, isFinite_time, findNucleus_time, isContracting_time)
    # degree: degree of tree, num_gens: # generators of tree, p: percentage of 1s (0-1)
    # num_elms_to_try: how many elements of the group to check if their order is infinite
    # section_depth: how far into the tree to go while checking if an elm's order is infinite
    # all times in seconds
    local new_autom_gr_fixed_ones, nucleusSize, isContractingTF, aut_gr, is_finite, nucleus_size, is_c, nucleus, timer_call;

    # helper methods
    new_autom_gr_fixed_ones := function(T_d, numGenerators, oneProb)
        # T_d: d-ary tree, numGenerators: <= 40,

        local possible_gens, possible_gens_no_id, generators, S_d, identity, weightedgenerators, num1s, 
        numOtherGen, currentGen, i, j, myGens, currentAut, RemoveRandom, elm, weightedSections, r;

        # ex: AutomatonGroup([ [ 1, 2, ()], [ 1, 2, (1,2) ] ], [ "a", "b" ]); (a=1, b=2, etc)
        # setup for a new automaton group
        possible_gens := ["1", "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t"]; # deal with 1!
        possible_gens_no_id := ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t"];

        # removes a random element from a list
        RemoveRandom := function(list)
            local i, element;
            i := Random([1..Length(list)]);
            element := list[i];
            list := Concatenation(list{[1..i-1]}, list{[i+1..Length(list)]});
            return [element, list];
        end;

        S_d := SymmetricGroup(T_d);
        currentAut := AutomatonGroup("1=(1,1)");

        while Size(GeneratorsOfGroup(currentAut)) <> numGenerators do
            # setup
            generators := [];

            identity := [];
            Append(identity, List([1..T_d], x -> 1));
            Append(identity, [One(S_d)]);
            Append(generators, [identity]);

            # getting correct number of 1s
            weightedSections := [];
            num1s := oneProb*(T_d*numGenerators*1.0);
            numOtherGen := (1-oneProb)*(T_d*numGenerators*1.0);

            # number of 1s and other gens
            if (num1s - Floor(num1s)) > (numOtherGen - Floor(numOtherGen)) then 
                num1s := Int(Ceil(num1s));
                numOtherGen := Int(Floor(numOtherGen));
            else
                num1s := Int(Floor(num1s));
                numOtherGen := Int(Ceil(numOtherGen));
            fi;

            Append(weightedSections, List([1..num1s], x -> 1));
            #Append(weightedSections, List([1..numOtherGen], x -> ((x) mod numGenerators) + 2));

            for i in [1..numOtherGen] do
                Append(weightedSections, [Random([2..numGenerators+1])]);
            od;

            # making lists
            for i in [2..(numGenerators+1)] do  # make some generators! skipping identity
                currentGen := [];

                for j in [1..T_d] do  # make some sections!
                    r := RemoveRandom(weightedSections);
                    elm := r[1];
                    weightedSections := r[2];
                    Append(currentGen, [elm]);
                od;

                Append(currentGen, [Random(S_d)]);  # appending random permutation!

                if currentGen in generators then
                    Remove(currentGen, Length(currentGen));
                    Append(currentGen, [Random(S_d)]);
                fi;

                Append(generators, [currentGen]);
            od;

            # getting generators
            myGens := List([1..(numGenerators+1)], i -> possible_gens[i]);

            # new automaton group!
            currentAut := AutomatonGroup(generators, myGens);
        od;

        return currentAut;
    end;

    nucleusSize := function(G)
        return Size(GroupNucleus(G));
    end;

    isContractingTF := function(G)
        local n;

        n := FindNucleus(G,false);

        return Length(n[1]);
    end;

    # getting your random autom group
    aut_gr := new_autom_gr_fixed_ones(degree, num_gens, p);

    is_finite := ""; # options: t/f/u/nc
    nucleus_size := -1;
    is_c := false;

    # TODO: checking if finite
    timer_call := IO_CallWithTimeoutList(rec(seconds := isFinite_time), IsFinite, [aut_gr]);
    if timer_call[1] and timer_call[2] then
        Print("Group is finite\n");
        is_finite := "t";
        is_c := true;

        # getting nucleus size
        nucleus := IO_CallWithTimeoutList(rec(seconds := findNucleus_time), nucleusSize, [aut_gr]);

        if nucleus[1] = true then     
            Print("found nucleus of finite group\n");
            nucleus_size := nucleus[2];
        fi;

        return [aut_gr, is_c, nucleus_size, is_finite];
    fi;

    # check if it's contracting (ADDED TIMER)
    # nucleus := FindNucleus(aut_gr, max_nucleus_size, false);
    nucleus := IO_CallWithTimeoutList(rec(seconds := isContracting_time), isContractingTF, [aut_gr]);

    if nucleus[1] = true then
        Print("Group is contracting\n");
        # contracting! yay!
        is_c := true;
        Print("\tNucleus size is", nucleus[2], "\n");
        nucleus_size  := nucleus[2];
        is_finite := "u";
        return [aut_gr, is_c, nucleus_size, is_finite];
    else
        Print("Group is not contracting\n");
        # not contracting
        is_finite := "nc";
        return [aut_gr, is_c, nucleus_size, is_finite]; # group, t/f contracting, nucleus size (-1 if nc), finite (nc: noncontracting)
    fi;
    return ["fail", "fail", "fail", "fail"];
end;

for i in [3,4,5,6,7,3,4,5,6,7] do
    p := 0.7; # (1.0*Random([1..100]))/100;
    T_d := i;
    num_generators := 5; # Random([1..10]);
    g := TestRandomGroup(T_d,num_generators, p, 3,3,3);
    Print(g, "\n");

    Print("\n------------------------------------------------------------------------------------------\n");
od;
