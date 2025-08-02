LoadPackage("AutomGrp");
OnBreak := function() QuitGap(); end;

TestOneGroup := function(degree, num_gens, p, isFinite_time, findNucleus_time, isContracting_time)
    # degree: degree of tree, num_gens: # generators of tree, p: percentage of 1s (0-1)
    # num_elms_to_try: how many elements of the group to check if their order is infinite
    # section_depth: how far into the tree to go while checking if an elm's order is infinite
    # all times in minutes
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
    timer_call := IO_CallWithTimeoutList(rec(minutes := isFinite_time), IsFinite, [aut_gr]);
    if timer_call[1] = fail then 
    	timer_call[1] := false;
    fi;
    if timer_call[1] and timer_call[2] then
        is_finite := "t";
        is_c := true;

        # getting nucleus size
        nucleus := IO_CallWithTimeoutList(rec(minutes := findNucleus_time), nucleusSize, [aut_gr]);

        if nucleus[1] = true then     
            nucleus_size := nucleus[2];
        fi;

        return [aut_gr, is_c, nucleus_size, is_finite];
    fi;

    # check if it's contracting (ADDED TIMER)
    # nucleus := FindNucleus(aut_gr, max_nucleus_size, false);
    nucleus := IO_CallWithTimeoutList(rec(minutes := isContracting_time), isContractingTF, [aut_gr]);

    if nucleus[1] = true then
        # contracting! yay!
        is_c := true;
        nucleus_size  := nucleus[2];
        if timer_call[1] and not timer_call[2] then 
            is_finite := "f";
        else 
            is_finite := "u";
        fi;
        return [aut_gr, is_c, nucleus_size, is_finite];
    else
        # not contracting
        is_finite := "nc";
        return [aut_gr, is_c, nucleus_size, is_finite]; # group, t/f contracting, nucleus size (-1 if nc), finite (nc: noncontracting)
    fi;
end;



NUMBER_TRIALS := 100;
DEGREE := 20;
NUM_GENERATORS := 10;
PROPORTION := 0.3;
CHECK_FINITE_TIME := 1;
FIND_NUCLEUS_TIME := 12;
PROPORTION_STRING := "0.3";


number_completed := 0;
filePath := Concatenation("./ContractingGroupsFound/", String(DEGREE), "_", String(NUM_GENERATORS), "_", PROPORTION_STRING, ".g");
contractingGroupsFile := OutputTextFile(filePath, true);
logFile := OutputTextFile("ContractingGroupsFound/contractingGroupsLog.txt", true);
AppendTo(filePath, "#--------------------NEW RUN--------------------\n");
AppendTo(filePath, "groupsFound := [");
numberContracting := 0;
numberContractingAndFinite := 0;
numberContractingAndInfinite := 0;
for trial in [1..NUMBER_TRIALS] do 
    result := TestOneGroup(DEGREE, NUM_GENERATORS, PROPORTION, CHECK_FINITE_TIME, FIND_NUCLEUS_TIME, FIND_NUCLEUS_TIME);
    if result[2] then 
        #group is contracting
        numberContracting := numberContracting + 1;
        if result[4] = "t" then 
            #group is finite
            AppendTo(filePath, "rec(automaton := ", AutomatonList(result[1]), ", nucleusSize := ", result[3], ", finite := true),\n");
            numberContractingAndFinite := numberContractingAndFinite + 1;
        elif result[4] = "f" then 
            #group is infinite
            AppendTo(filePath, "rec(automaton := ", AutomatonList(result[1]), ", nucleusSize := ", result[3], ", finite := false),\n");
            numberContractingAndInfinite := numberContractingAndInfinite + 1;
        else 
            #unkown whether group is finite or not
            AppendTo(filePath, "rec(automaton := ", AutomatonList(result[1]), ", nucleusSize := ", result[3], "),\n");
        fi;
    fi;
    CloseStream(contractingGroupsFile);
    contractingGroupsFile := OutputTextFile(filePath, true);
od;
AppendTo(filePath, "];");
AppendTo("ContractingGroupsFound/contractingGroupsLog.txt", "For degree ", DEGREE, ", with ", NUM_GENERATORS, " generators and p = ", PROPORTION_STRING, ", ", numberContracting, " out of ", NUMBER_TRIALS, " groups were contracting, of which ", numberContractingAndFinite, " were found to be finite and ", numberContractingAndInfinite, " were found to be infinite.\n\n");
CloseStream(contractingGroupsFile);
CloseStream(logFile);
