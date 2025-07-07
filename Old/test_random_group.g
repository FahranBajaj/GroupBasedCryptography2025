
TestRandomGroup := function(degree, num_gens, p, max_nucleus_size, num_elms_to_try, section_depth, max_time)
    # degree: degree of tree, num_gens: # generators of tree, p: percentage of 1s (0-1)
    # num_elms_to_try: how many elements of the group to check if their order is infinite
    # section_depth: how far into the tree to go while checking if an elm's order is infinite
    # max_time: in seconds
    local new_autom_gr_fixed_ones, ElmOfInfiniteOrderTF, aut_gr, is_finite, nucleus_size, is_c, nucleus, inf_elm, timer_call;

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

                Append(currentGen, [Random(Elements(S_d))]);  # appending random permutation!

                if currentGen in generators then
                    Remove(currentGen, Length(currentGen));
                    Append(currentGen, [Random(Elements(S_d))]);
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

    ElmOfInfiniteOrderTF := function(aut_gr, num_elms_to_try, section_depth)
        local infElm;

        infElm := FindElementOfInfiniteOrder(aut_gr, num_elms_to_try, section_depth);

        if infElm <> fail then
            return true;
        fi;

        return false;
    end;

    # getting your random autom group
    aut_gr := new_autom_gr_fixed_ones(degree, num_gens, p);

    is_finite := ""; # options: t/f/u/nc
    nucleus_size := -1;
    is_c := false;

    # check if it's contracting
    nucleus := FindNucleus(aut_gr, max_nucleus_size, false);

    if nucleus <> fail then
        # contracting! yay!
        is_c := true;
        nucleus_size  := Length(nucleus[1]);
    else
        # not contracting
        is_finite := "nc";
        return [aut_gr, is_c, nucleus_size, is_finite]; # group, t/f contracting, nucleus size (-1 if nc), finite (nc: noncontracting)
    fi;

    # if contracting, is the group infinite or finite?
    
    # checking if infinite

    timer_call := IO_CallWithTimeoutList(rec(seconds := max_time), ElmOfInfiniteOrderTF, [aut_gr, num_elms_to_try, section_depth]);
    
    if timer_call[1] and timer_call[2] then
        is_finite := "f";
        return [aut_gr, is_c, nucleus_size, is_finite];
    fi;

    timer_call := IO_CallWithTimeoutList(rec(seconds := max_time), IsFractal, [aut_gr]);

    if timer_call[1] and timer_call[2] then
        is_finite := "f";
        return [aut_gr, is_c, nucleus_size, is_finite];
    fi;

    # TODO: checking if finite
    timer_call := IO_CallWithTimeoutList(rec(seconds := max_time), IsFinite, [aut_gr]);
    if timer_call[1] and timer_call[2] then
        is_finite := "t";
        return [aut_gr, is_c, nucleus_size, is_finite];
    fi;

    # undetermined
    is_finite := "u";
    return [aut_gr, is_c, nucleus_size, is_finite];
end;
