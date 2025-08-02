#read in groups from files
LoadPackage("AutomGrp");
NUMBER_TRIALS := 100;
DEGREES := [3, 7, 12, 20];
NUM_GENERATORS := [3, 7, 10];
PROPORTIONS := ["0.3", "0.7", "0.9"];

#dictionary allowing us to write groups to file in same order as read
groupToIndex := NewDictionary(AutomatonGroup("a = (1, 1)"), true);
allGroups := NewDictionary(rec(degree := 3, num_generators := 3, proportionString := "0.9"), true);
groupsOfUnknownSize := [];

for degree in DEGREES do
    for num_generators in NUM_GENERATORS do 
        for proportionString in PROPORTIONS do 
            if degree = 3 and num_generators = 10 and proportionString = "0.9" then 
                continue;
            fi;
            filePath := Concatenation("./ContractingGroupsFound/", String(degree), "_", String(num_generators), "_", proportionString, ".g");
            dictRec := rec(degree := degree, num_generators := num_generators, proportionString := proportionString);
            #this file gives us the list groupsFound
            AddDictionary(allGroups, dictRec, []);
            Read(filePath);
            for i in [1..Length(groupsFound)] do 
                group := AutomatonGroup(groupsFound[i].automaton);
                otherGroups := LookupDictionary(allGroups, dictRec);
                Append(otherGroups, [group]);
                AddDictionary(allGroups, dictRec, otherGroups);
                nucleusSize := groupsFound[i].nucleusSize;
                if IsBound(groupsFound[i].finite) then 
                    AddDictionary(groupToIndex, group, rec(degree := degree, num_generators := num_generators, proportionString := proportionString, nucleusSize := nucleusSize, finite := groupsFound[i].finite));
                else 
                    AddDictionary(groupToIndex, group, rec(degree := degree, num_generators := num_generators, proportionString := proportionString, nucleusSize := nucleusSize));
                    Append(groupsOfUnknownSize, [group]);
                fi;
            od;
        od;
    od;
od;

Print("After reading in files, there are ", Length(groupsOfUnknownSize), " groups to test.\n");

#first step: call isFractal for a while
MAX_FRACTAL_TIME := 10;
#reverse because we will be removing elements from the list 
for i in Reversed([1..Length(groupsOfUnknownSize)]) do 
    group := groupsOfUnknownSize[i];
    timer_call := IO_CallWithTimeout(rec(seconds := MAX_FRACTAL_TIME), IsFractal, group);
    if timer_call[1] and timer_call[2] then 
        #group is infinite
        Remove(groupsOfUnknownSize, i);
        record := LookupDictionary(groupToIndex, group);
        record.finite := false;
        AddDictionary(groupToIndex, group, record);
    fi;
od;

Print("After using isFractal, there are ", Length(groupsOfUnknownSize), " groups to test.\n");

AllElementsOfInfiniteOrder := function(MAX_ELM_INF_ORDER_TIME, depth, width)
    # MAX_ELM_INF_ORDER_TIME: in HOURS
    # depth: list with 4 integers in inc. order
    # width: list with 4 integers in inc. order

    local ElmOfInfiniteOrderTF, AllElmsOfInfiniteOrder, extra_time, times, j, i, group, timer_call, record;

    # helper method
    ElmOfInfiniteOrderTF := function(G, start, stop)
        local tf;

        tf := FindElementOfInfiniteOrder(G, start, stop);
        if tf <> fail then
            return true;
        fi;
        return false;
    end;

    AllElmsOfInfiniteOrder := function(startList, stopList, totalTime)
        local initial_num, initial_time, times, i, group, extra_time, timer_call;

        initial_num := Length(groupsOfUnknownSize)*1.0;
        initial_time := totalTime/initial_num;
        times := List([1..Length(groupsOfUnknownSize)], t -> initial_time);

        for i in Reversed([1..Length(groupsOfUnknownSize)]) do 
            group := groupsOfUnknownSize[i];
            extra_time := Runtime();
            timer_call := IO_CallWithTimeout(rec(hours := times[i]), ElmOfInfiniteOrderTF, group, depth[j], width[j]);
            extra_time := Runtime() - extra_time;

            # converting time to hours
            extra_time := times[i] - extra_time * 0.001 / 3600.0;

            if timer_call[1] and timer_call[2] then 
                #group is infinite
                Remove(groupsOfUnknownSize, i);
                record := LookupDictionary(groupToIndex, group);
                record.finite := false;
                AddDictionary(groupToIndex, group, record);
            fi;

            if timer_call[1] <> false then
                if 1.0*i <> 1.0 then
                    extra_time := extra_time / (1.0*i - 1.0);
                    times := List(times, t -> t + extra_time);
                fi;
            fi;
        od;

    end;

    extra_time := 0;
    times := List([1..4], i -> MAX_ELM_INF_ORDER_TIME*1.0);

    for j in [1..4] do  # each h/d pair
        extra_time := Runtime();
        timer_call := IO_CallWithTimeout(rec(hours := times[j]), AllElmsOfInfiniteOrder, depth[j], width[j], times[j]);
        extra_time := Runtime() - extra_time;

        # converting time to hours and getting extra time
        extra_time := times[j] - extra_time * 0.001 / 3600.0;

        if j <> 4 then
            extra_time := extra_time / (1.0*(4-j));
            times := List(times, t -> t + extra_time);
        fi;
    od;
end;

AllElementsOfInfiniteOrder(6, [2, 3, 4, 5], [2, 3, 4, 5]);
logFile := OutputTextFile("ContractingGroupsFound/contractingGroupsLog.txt", true);
AppendTo("ContractingGroupsFound/contractingGroupsLog.txt", "#--------------------Part 2--------------------\n");
parametersStarted := NewDictionary(rec(degree := 3, num_generators := 3, proportionString := "0.9"), false);

for degree in DEGREES do
    for num_generators in NUM_GENERATORS do 
        for proportionString in PROPORTIONS do 
            if degree = 3 and num_generators = 10 and proportionString = "0.9" then 
                continue;
            fi;
            filePath := Concatenation("./ContractingGroupsFound/", String(degree), "_", String(num_generators), "_", proportionString, "(2).g");
            contractingGroupsFile := OutputTextFile(filePath, true);
            dictRec := rec(degree := degree, num_generators := num_generators, proportionString := proportionString);
            groups := LookupDictionary(allGroups, dictRec);
            numberContracting := Length(groups);
            numberContractingAndFinite := 0;
            numberContractingAndInfinite := 0;
            AppendTo(filePath, "groupsFound := [");
            for group in groups do 
                groupRec := LookupDictionary(groupToIndex, group);
                if IsBound(groupRec.finite) then 
                    if groupRec.finite then 
                        #group is finite
                        numberContractingAndFinite := numberContractingAndFinite + 1;
                        AppendTo(filePath, "rec(automaton := ", AutomatonList(group), ", nucleusSize := ", groupRec.nucleusSize, ", finite := true),\n");
                    else 
                        #group is infinite
                        numberContractingAndInfinite := numberContractingAndInfinite + 1;
                        AppendTo(filePath, "rec(automaton := ", AutomatonList(group), ", nucleusSize := ", groupRec.nucleusSize, ", finite := false),\n");
                    fi;
                else 
                    #unkown size
                    AppendTo(filePath, "rec(automaton := ", AutomatonList(group), ", nucleusSize := ", groupRec.nucleusSize, "),\n");
                fi;
            od;
            AppendTo(filePath, "];");
            CloseStream(contractingGroupsFile);
            AppendTo("ContractingGroupsFound/contractingGroupsLog.txt", "For degree ", degree, ", with ", num_generators, " generators and p = ", proportionString, ", ", numberContracting, " out of ", NUMBER_TRIALS, " groups were contracting, of which ", numberContractingAndFinite, " were found to be finite and ", numberContractingAndInfinite, " were found to be infinite.\n\n");
        od;
    od;
od;
CloseStream(logFile);
