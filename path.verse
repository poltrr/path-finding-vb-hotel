using { /Fortnite.com/Devices }
using { MinHeap }
using { /UnrealEngine.com/Temporary/SpatialMath }
using { /Verse.org/Random }
using { /Verse.org/Simulation }
using { /Verse.org/Simulation/Tags }

path_node := class<unique>:
    ## The position of the node.
    Translation<public> : vector3
    ## Describes if the node has a vertical connection.
    IsVertical<public> : logic = false

    ## The current players at this node.
    var Players<private> : []player = array{}

    #############
    ## Methods ##
    #############

    ## Returns the shortest distance to another node.
    DistanceTo<public>(Destination : path_node)<transacts> : float =
        Distance(Translation, Destination.Translation)
    
    ## Adds a player to this node.
    AddPlayer<public>(Player : player) : void =
        set Players += array{Player}
    
    ## Removes a player from this node.
    RemovePlayer<public>(Player : player)<transacts><decides> : void =
        set Players = Players.RemoveFirstElement[Player]
    
    #############
    ## Getters ##
    #############

    GetPlayers<public>()<transacts> : []player = Players

path_connection_tag := enum:
    Default
    Player
    Unreachable

path_connection := struct:
    Node<public> : path_node
    Tag<public> : path_connection_tag = path_connection_tag.Default

## A representation of a path.
path := class:
    var MaybeAdjacencyList<private> : ?[path_node][]path_connection = false
    
    #############
    ## Methods ##
    #############

    ## Returns the children of a given Node, with the tag Default.
    ## Adding an optional tag also returns all nodes with that tag.
    GetChildren<public>(
        Node : path_node, 
        ?Tag : path_connection_tag = path_connection_tag.Default
    )<transacts><decides> : []path_node =
        for:
            Connection : GetAdjacencyList[][Node]
            Connection.Tag = Tag or Connection.Tag = path_connection_tag.Default
        do:
            Connection.Node
    
    ## Returns the path height, at a certain point, from the node.
    ##
    ## Returns node height if the path node isn't vertical.
    ## Returns the interpolated height to its pair node, if vertical.
    GetHeightAt<public>(Node: path_node, Target : vector3)<transacts> : float =
        Translation : vector3 = Node.Translation

        # Calculate height if node is vertical.
        if (Node.IsVertical?):
            # Find pair vertical node, to calculate height.
            for (Neighbor : GetChildren[Node]; Neighbor.IsVertical?):
                NeighborTranslation := Neighbor.Translation
                
                # Displacement between both nodes.
                dX : float = Abs(Translation.X - NeighborTranslation.X)
                dY : float = Abs(Translation.Y - NeighborTranslation.Y)
                dZ : float = Abs(Translation.Z - NeighborTranslation.Z)
                # The height of the bottom node.
                BottomZ : float = Min(Translation.Z, NeighborTranslation.Z)

                # Stores values for the slope's coordinate direction (X or Y).
                dCoord : float = Max(dX, dY)
                TargetCoord : float = if (dX > dY) then Target.X else Target.Y
                Coord : float = if (dX > dY) then Translation.X else Translation.Y
                NeighborCoord : float =
                    if (dX > dY) 
                    then NeighborTranslation.X 
                    else NeighborTranslation.Y
                BottomCoord : float = 
                    if (Translation.Z < NeighborTranslation.Z)
                    then Coord
                    else NeighborCoord
                
                # Calculate height if Target is between the nodes.
                if (
                    dCoord > 0.0
                    TargetCoord > Coord and
                    TargetCoord < NeighborCoord or
                    TargetCoord < Coord and 
                    TargetCoord > NeighborCoord
                ):
                    dTarget : float = Abs(BottomCoord - TargetCoord)
                    # Returns the interpolated height.
                    return (dTarget / dCoord) * dZ + BottomZ
            
            Translation.Z
        else:
            Translation.Z
    
    ## Returns an array representing a path from the Start node to the End node.
    ## Succeeds if the shortest path (most of the time) is found.
    ## Fails if no possible path is found.
    FindPath<public>(Start : path_node, End : path_node)<transacts><decides> : []path_node =
        # Priority queue of path_node_data to search.
        ToSearch : min_heap_path_node_data = min_heap_path_node_data{}
        # A map linking all path_node_data to their respective path_node.
        var Nodes : [path_node]path_node_data = map{}
        # A set of all processed path_node_data.
        var Processed : [path_node_data]logic = map{}
        # An array of path_node representing the path from the End to the Start.
        var MaybeBackwardsPathData : ?[]path_node_data = false

        # Creates path_node_data for the Start node, and inserts into ToSearch.
        StartData := MakePathNodeData(Start, End)
        StartData.SetG(0.0)
        ToSearch.Push[StartData]
        # Links Start path_node to its path_node_data.
        set Nodes[Start] = StartData

        loop:
            if:
                CurrentData : path_node_data = ToSearch.Top[]
                ToSearch.Pop[]
                set Processed[CurrentData] = true
                CurrentNode : path_node = CurrentData.Node
            then:
                # Stores the backwards path if the End node is reached.
                if (CurrentNode = End):
                    var CurrentPathData : path_node_data = CurrentData
                    var BackwardsPathData : []path_node_data = 
                        array{CurrentPathData}
                    # Navigates from the End to all previous nodes, and stores 
                    # them into an array.
                    loop:
                        if:
                            PreviousPathData : path_node_data = 
                                CurrentPathData.GetPrevious[]
                            not PreviousPathData = Start
                        then:
                            set BackwardsPathData += array{PreviousPathData}
                            set CurrentPathData = PreviousPathData
                        else:
                            set MaybeBackwardsPathData = 
                                option{BackwardsPathData}
                            break
                    break
                for (
                    NeighborNode : GetChildren[CurrentNode]
                    # Gets the neighbor's path_node_data.
                    # If no path_node_data is found, create one and store it.
                    NeighborData : path_node_data = 
                        if (Data : path_node_data = Nodes[NeighborNode])
                        then Data
                        else MakePathNodeData(NeighborNode, End)
                    not Processed[NeighborData]
                    # Calculates new G cost from the current node.
                    NewG : float = 
                        CurrentData.GetG[] + 
                        CurrentNode.DistanceTo(NeighborNode)
                    # Filter for nodes with higher G cost.
                    # New nodes with new path_node_data will also succeed.
                    not NeighborData.GetG[] >= NewG
                ):
                    # Sets the neighbor's G cost and previous node.
                    NeighborData.SetG(NewG)
                    NeighborData.SetPrevious(CurrentData)
                    # Add neighbor to Nodes and ToSearch if not already.
                    if:
                        not Nodes[NeighborNode]
                        set Nodes[NeighborNode] = NeighborData
                        ToSearch.Push[NeighborData]
            else:
                break
        
        LastIndex : int = MaybeBackwardsPathData?.Length - 1
        # Returns reversed backwards path, i.e. the fordwards path.
        for (Index := 0..LastIndex):
            MaybeBackwardsPathData?[LastIndex - Index].Node
    
    #############
    ## Getters ##
    #############

    GetAdjacencyList<public>()<transacts><decides> : [path_node][]path_connection = MaybeAdjacencyList?
    
    #############
    ## Setters ##
    #############

    SetAdjacencyList<public>(NewAdjacencyList : [path_node][]path_connection)<transacts> : void =
        set MaybeAdjacencyList = option{NewAdjacencyList}

## A helper class that contains the node data to perform the A* algorithm.
path_node_data := class<final><unique>:
    Node : path_node
    H : float
    var MaybeG<private> : ?float = false
    var MaybePrevious<private> : ?path_node_data = false

    #############
    ## Methods ##
    #############

    ## Succeeds if it's lesser than the compare path node data.
    IsLessThan<public>(Compare : path_node_data)<transacts><decides> : void =
        GetF[] < Compare.GetF[] or 
        GetF[] = Compare.GetF[] and H < Compare.H
    
    ## Succeeds if it's greater than the compare path node data.
    IsGreaterThan<public>(Compare : path_node_data)<transacts><decides> : void =
        GetF[] > Compare.GetF[] or 
        GetF[] = Compare.GetF[] and H > Compare.H

    #############
    ## Getters ##
    #############

    GetG<public>()<transacts><decides> : float = MaybeG?
    GetF<public>()<transacts><decides> : float = MaybeG? + H
    GetPrevious<public>()<transacts><decides> : path_node_data = MaybePrevious?

    #############
    ## Setters ##
    #############

    SetG<public>(G : float)<transacts> : void =
        set MaybeG = option{G}
    SetPrevious<public>(Previous : path_node_data)<transacts> : void =
        set MaybePrevious = option{Previous}

MakePathNodeData<constructor>(Node : path_node, EndNode : path_node)<transacts> := path_node_data:
    Node := Node
    H := Node.DistanceTo(EndNode)
