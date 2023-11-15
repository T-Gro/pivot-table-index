// For more information see https://aka.ms/fsharp-console-apps
module PivotTableProgram
open System


let inline square x = x * x
let inline vSnd (struct(_,y)) = y
let inline vFst (struct(x,_)) = x

[<AutoOpen>]
module Types = 
    open System.Collections.Generic

    type Distance = float
    type LowerBound = Distance
    type Vector = float array
    type NormalizedVector = Vector
    type DistanceCalculations = {ToPivots:int;ToDataset:int}

    type ResultsAccumulator = SortedSet<struct(int * Distance)>
    let createAccumulator() = new ResultsAccumulator(ComparisonIdentity.FromFunction(fun struct(_,d1) struct(_,d2) -> if d1=d2 then 0 else if d1 < d2 then -1 else 1))


[<AutoOpen>]
module VectorOperations = 
    let vectorLength (vector: Vector) = 
        vector 
        |> Array.sumBy square
        |> sqrt

    let normalizeVector (vector: Vector) =         
        let sum = vectorLength vector
        if sum = 0.0 || sum = 1.0 then 
            vector
        else 
            vector |> Array.map (fun x -> x / sum)

module DistanceFunctions = 
    
    let euclidean (v1 : NormalizedVector) (v2: NormalizedVector) : Distance = 
        let mutable sum = 0.0
        (v1, v2) ||> Array.iter2 (fun x y -> sum <- sum + ((x - y) |> square))
        sum |> sqrt

module MIndex = 
    

    type PivotIndex = int
    [<Struct>]
    type DataNode = {DbIdx : int; PivotDistances : Distance array; Permutation : PivotIndex array}
    type Level = int
    

    type LookupTree = 
        | Leaf of level:Level * data:DataNode array
        | InnerNode of level:Level * children:Map<PivotIndex,LookupTree>

    type DB = {Tree:LookupTree; Pivots : NormalizedVector array; Database : NormalizedVector array}

    let createIndexRandomizedPivots (pivotCount: int) (dataset: NormalizedVector array) (bucketLimit:int) = 
        let rnd = new Random(42)
        let pivots = Array.init pivotCount (fun _ -> dataset.[rnd.Next(dataset.Length)])

        let idx = 
            dataset
            |> Array.Parallel.map (fun v -> pivots |> Array.map (fun p -> DistanceFunctions.euclidean p v))
            |> Array.mapi (fun i row ->
                { DbIdx = i
                  PivotDistances = row
                  Permutation = 
                    row 
                    |> Array.mapi (fun i d -> struct(i,d)) 
                    |> Array.sortBy vSnd
                    |> Array.map vFst })

        let tree = Leaf(level=0,data = idx)

        
        let rec fixUpTree (t:LookupTree) = 
            match t with
            | Leaf(level,data) when data.Length > bucketLimit && level < pivotCount ->
                let separatedKids = 
                    data 
                    |> Array.groupBy (fun d -> d.Permutation[level])
                    |> Array.map (fun (k,data) -> k,Leaf(level+1,data))
                    |> Map.ofArray
                let newInnerNode = InnerNode(level,separatedKids)
                fixUpTree newInnerNode
            | InnerNode(level,children) ->
                let newChildren = children |> Map.map (fun _ tree -> fixUpTree tree )
                InnerNode(level,newChildren)
            | _ -> t

        {Tree = fixUpTree tree; Pivots = pivots; Database = dataset}

    let approxKnnQuery (queryObject : NormalizedVector, db : DB, k : int) =
        let distanceToQuery = DistanceFunctions.euclidean queryObject
        let pivotPermutation = 
            db.Pivots
            |> Array.mapi (fun i p -> struct(i,distanceToQuery p))
            |> Array.sortBy vSnd
            |> Array.map vFst

        let results = createAccumulator()

        let rec collectResults idx tree = 
            match tree with
            | Leaf(_,data) -> 
                for d in data do
                    results.Add(struct(d.DbIdx, distanceToQuery (db.Database[d.DbIdx]))) |> ignore<bool>
            | InnerNode(level,children) when children.ContainsKey(pivotPermutation[idx]) ->
                collectResults (idx+1) (children.[pivotPermutation[idx]])
                while results.Count < k then
                    collectResults (idx+)
            | InnerNode(level,children) when idx < db.Pivots.Length ->
                ()
                

        collectResults 0 db.Tree


module PivotTable = 
    open System.Collections.Generic
    
    type Pivots = NormalizedVector array
    type DB = { Pivots : NormalizedVector array; PivotTable : Distance array array; Database : NormalizedVector array }

    let createIndexRandomizedPivots (pivotCount: int) (dataset: NormalizedVector array) : DB = 
        let rnd = new Random(42)

        let pivots = Array.init pivotCount (fun _ -> dataset.[rnd.Next(dataset.Length)])

        let idx = 
            dataset
            |> Array.Parallel.map (fun v -> pivots |> Array.map (fun p -> DistanceFunctions.euclidean p v))

        { Pivots = pivots; PivotTable = idx; Database = dataset}

    let createIndex (pivotCount: int) (dataset: NormalizedVector array) : DB = 

        let idx = Array.init dataset.Length (fun _ -> Array.zeroCreate pivotCount)
        let pivots = Array.zeroCreate pivotCount
        let pivotIds = Array.zeroCreate pivotCount

        let addPivot n (datasetId: int) =             
            let pivot = dataset[datasetId]
            pivots.[n] <- pivot
            dataset |> Array.iteri (fun rowIdx v -> idx.[rowIdx].[n] <- DistanceFunctions.euclidean pivot v )          
            pivotIds.[n] <- datasetId
            
        addPivot 0 0
        for newPivotNumber=1 to pivotCount-1 do
            
            let mutable maxDistance : Distance = Double.MinValue
            let mutable idOfMax : int = 0

            for rowIdx=1 to dataset.Length-1 do
                if pivotIds |> Array.contains rowIdx then 
                    ()                
                else
                    let mutable distanceToExistingPivots : Distance = 0.0
                    for existingPivotIdx=0 to newPivotNumber-1 do
                        distanceToExistingPivots <- distanceToExistingPivots + (square idx.[rowIdx].[existingPivotIdx])
              
                    if distanceToExistingPivots > maxDistance then 
                        maxDistance <- distanceToExistingPivots
                        idOfMax <- rowIdx
            
            addPivot newPivotNumber idOfMax         

        { Pivots = pivots; PivotTable = idx; Database = dataset}

    let inline createLowerBounds (db : DB) (distanceToQuery)  = 
        let distancesToPivots = db.Pivots |> Array.map distanceToQuery
        let lowerBounds = 
            db.PivotTable
            |> Array.mapi (fun idx row ->
                // Utilize triangle inequality between pre-computed distances to pivots and distances between pivots and the query object
                let mutable maxLb : LowerBound = 0.0
                Array.iter2 (fun d p -> maxLb <- max maxLb (abs (d - p))) distancesToPivots row
                struct(idx,maxLb))

        lowerBounds |> Array.sortInPlaceBy (fun struct(_idx,lb) -> lb)
        lowerBounds

    let naiveKnnQuery (queryObject : NormalizedVector, db : DB, k : int) = 
        let distanceToQuery = DistanceFunctions.euclidean queryObject
        let acc = createAccumulator()

        db.Database
        |> Array.mapi (fun i r -> struct(i, distanceToQuery r))
        |> Array.sortBy vSnd
        |> Array.take k
        |> acc.UnionWith

        acc, {ToPivots = 0;ToDataset = db.Database.Length}

    let knnQuery (queryObject : NormalizedVector, db : DB, k : int) = 
        let distanceToQuery = DistanceFunctions.euclidean queryObject
        let lowerBounds = createLowerBounds db distanceToQuery
             
        let rec fillKnnResults idx (resultsSoFar: ResultsAccumulator) =  
            let struct(dbIdx,lowerBound) = lowerBounds.[idx]
            let currentMaxDistance : Distance =
                match resultsSoFar.Count with
                | 0 -> Double.MaxValue
                | _ -> resultsSoFar.Max |> vSnd

            // We can stop as soon as the lowerbound (= always lower) is higher than the current Kth result
            if currentMaxDistance <= lowerBound && resultsSoFar.Count >= k then                 
                resultsSoFar, {ToPivots = db.Pivots.Length;ToDataset = idx}
            else
                let calculatedDistance = distanceToQuery (db.Database[dbIdx])
                assert(calculatedDistance >= lowerBound)

                if resultsSoFar.Count < k then 
                    resultsSoFar.Add(struct(dbIdx,calculatedDistance)) |> ignore<bool>
                else           
                    if currentMaxDistance > calculatedDistance then 
                        resultsSoFar.Remove(resultsSoFar.Max) |> ignore<bool>
                        resultsSoFar.Add(struct(dbIdx,calculatedDistance)) |> ignore<bool>

                match idx + 1 with
                | nextIdx when nextIdx < lowerBounds.Length -> fillKnnResults nextIdx resultsSoFar
                | _ -> resultsSoFar, {ToPivots = db.Pivots.Length;ToDataset = idx+1}


        
        fillKnnResults 0 (createAccumulator())

module TestData = 
    open FSharp.Data
    open System.IO

    [<Literal>]
    let path = __SOURCE_DIRECTORY__ + "/food.json"
    type FoodType = JsonProvider<Sample=path>

    [<Literal>]
    let issuesPath = __SOURCE_DIRECTORY__ + "/issues-sample.json"
    type GhIssuesType = JsonProvider<Sample=issuesPath>

    let getIssuesVectors() = 
        let fullFile = GhIssuesType.Load(issuesPath.Replace("issues-sample","issues"))
        fullFile
        |> Array.collect (fun iss -> 
            iss.Chunks 
            |> Array.map (fun x -> x.Embedding) 
            |> Array.filter (fun x -> x.Length > 0))

    let getFoodVectors() = 
        let fullFile = FoodType.Load(path)
        fullFile
        |> Array.map (fun food -> food.Embedding |> normalizeVector)

    let randomData() = 
        let rnd = new Random(2112)
        let vectorSize = 4
        let databaseSize = 10_000

        let normalizedDataset = 
            Array.init databaseSize (fun _ -> 
                Array.init vectorSize (fun _ -> rnd.NextDouble()) |> normalizeVector)

        normalizedDataset


[<EntryPoint>]
let main argv =    
    
    let normalizedDataset = TestData.getIssuesVectors()
    let queries = 100
    let rnd = new Random(2112)
    let sampleQueries = Array.init queries (fun _ -> normalizedDataset[rnd.Next(normalizedDataset.Length)])
    printfn "Random dataset created"
    printfn "------------------------"    

    let runTest name db = 

        printfn "Index  created :: %s" name
        printfn "------------------------"


        let overlapSizes = ResizeArray()

        for q in sampleQueries do
            let res,pivotCalculations = PivotTable.knnQuery (q, db, 20)
            let naive,_ = PivotTable.naiveKnnQuery (q, db, 20)

            let overlap = res |> Seq.sumBy (fun r -> if naive.Contains(r) then 1 else 0)
            overlapSizes.Add({|pivotCalculations with Overlap = overlap|})        

        printfn "Queries  finished :: %s" name
        printfn "------------------------"

        let groups = 
            overlapSizes
            |> Seq.groupBy (fun x -> x.Overlap)
            |> Seq.toList
            |> List.sortByDescending fst

        for (overlap,x) in groups do 
            let averageDistances = x |> Seq.averageBy (fun x -> float x.ToDataset)
            let averagePivotDistances = x |> Seq.averageBy (fun x -> float x.ToPivots)

            printfn $"{overlap} overlap:  {x |> Seq.length} queries ;;  {averageDistances}+{averagePivotDistances} = {averageDistances+averagePivotDistances} distance calculations"

        printfn "----------- :: %s :: finished -------------" name

    runTest "256 iterative pivots" (PivotTable.createIndex 256 normalizedDataset)
    runTest "512 iterative pivots" (PivotTable.createIndex 512 normalizedDataset)
    runTest "1024 iterative pivots" (PivotTable.createIndex 1024 normalizedDataset)

  
    runTest "256 random pivots" (PivotTable.createIndexRandomizedPivots 256 normalizedDataset)
    runTest "512 random pivots" (PivotTable.createIndexRandomizedPivots 512 normalizedDataset)
    runTest "1024 random pivots" (PivotTable.createIndexRandomizedPivots 1024 normalizedDataset)

    42