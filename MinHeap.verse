## Module containing implementations for min heaps.
MinHeap := module:
    ## A type to encapsulate two child indexes.
    indexes := tuple(int, int)

    #############
    ## Classes ##
    #############
    
    ## Min heap implementation for path_node_data type.
    min_heap_path_node_data<public> := class<final><concrete>():
        ## Array representation of a heap tree.
        var HeapArray<private> : []path_node_data = array{}

        #############
        ## Methods ##
        #############
    
        ## Returns the minimum value of the heap.
        Top<public>()<transacts><decides> : path_node_data =
            HeapArray[0]
        
        ## Removes the minimum value from the heap.
        Pop<public>()<transacts><decides> : void =
            LastIndex : int = HeapArray.Length - 1
            Swap[0, LastIndex]
            set HeapArray = HeapArray.RemoveElement[LastIndex]
            if (not Empty[]):
                SiftDown[0]
        
        ## Inserts a new value into the heap, and changes the order accordingly.
        Push<public>(Value : path_node_data)<transacts><decides> : void =
            set HeapArray += array{Value}
            SiftUp[HeapArray.Length - 1]
        
        ## Returns the amount of elements in the heap.
        Size<public>()<transacts> : int = 
            HeapArray.Length
        
        ## Succeeds if there are no elements in the heap.
        Empty<public>()<transacts><decides> : void =
            Size() = 0
        
        ## Given the index of a value, move up its position until it's correctly 
        ## positioned.
        SiftUp<private>(Index : int)<transacts><decides> : void =
            var CurrentIndex : int = Index
            var CurrentValue : path_node_data = HeapArray[CurrentIndex]
            var ParentIndex : int = GetParentIndex[CurrentIndex]
            
            var ShouldRollback : logic = false
            loop:
                if:
                    var ParentValue : path_node_data = HeapArray[ParentIndex]
                    CurrentValue.IsLessThan[ParentValue]
                then:
                    if:
                        Swap[CurrentIndex, ParentIndex]
                        set CurrentIndex = ParentIndex
                        set ParentIndex = GetParentIndex[CurrentIndex]
                    else:
                        set ShouldRollback = true
                        break
                else:
                    break
            not ShouldRollback?
        
        ## Given the index of a value, move down its position until it's correctly 
        ## positioned.
        SiftDown<private>(Index : int)<transacts><decides> : void =
            # Indexes
            var CurrentIndex : int = Index
            ChildrenIndexes : indexes = GetChildrenIndexes[CurrentIndex]
            var LeftIndex : int = ChildrenIndexes(0)
            var RightIndex : int = ChildrenIndexes(1)
            # Values
            var CurrentValue : path_node_data = HeapArray[CurrentIndex]
            
            HeapLength : int = HeapArray.Length
            var ShouldRollback : logic = false
            loop:
                if:
                    LeftIndex < HeapLength and
                    CurrentValue.IsGreaterThan[HeapArray[LeftIndex]] or
                    RightIndex < HeapLength and
                    CurrentValue.IsGreaterThan[HeapArray[RightIndex]]
                then:
                    if:
                        Smallest : int = 
                            if:
                                RightIndex >= HeapLength or 
                                HeapArray[LeftIndex].IsLessThan[HeapArray[RightIndex]]
                            then: 
                                LeftIndex 
                            else: 
                                RightIndex
                        Swap[CurrentIndex, Smallest]
                        set CurrentIndex = Smallest
                        NewChildrenIndexes : indexes = GetChildrenIndexes[CurrentIndex]
                        set LeftIndex = NewChildrenIndexes(0)
                        set RightIndex = NewChildrenIndexes(1)
                    else:
                        set ShouldRollback = true
                        break
                else:
                    break
            not ShouldRollback?
        
        ## Given the index of a value, returns the index of its parent.
        GetParentIndex<private>(Index : int)<transacts><decides> : int =
            Floor((Index - 1) / 2)
        
        ## Given the index of a value, returns the indexes of its children.
        GetChildrenIndexes<private>(Index : int)<transacts><decides> : indexes =
            LeftIndex : int = 2 * Index + 1
            (LeftIndex, LeftIndex + 1)
        
        ## Swaps two values in the heap.
        Swap<private>(LIndex : int, RIndex : int)<transacts><decides> : void =
            LValue : path_node_data = HeapArray[LIndex]
            set HeapArray[LIndex] = HeapArray[RIndex]
            set HeapArray[RIndex] = LValue
