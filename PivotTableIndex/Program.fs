// For more information see https://aka.ms/fsharp-console-apps
module PivotTableProgram
open System

let inline square x = x * x
let inline vSnd (struct(_,y)) = y

[<AutoOpen>]
module Types = 
    type Distance = float
    type LowerBound = Distance
    type Vector = float array
    type NormalizedVector = Vector

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
        sqrt sum

module PivotTable = 
    open System.Collections.Generic

    type Pivots = NormalizedVector array
    type DB = { Pivots : NormalizedVector array; PivotTable : Distance array array; Database : NormalizedVector array }

    type ResultsAccumulator = SortedSet<struct(int * Distance)>

    let pickPivots (dataset: NormalizedVector array) (pivotCount: int) = 
        let random = Random(42)
        Array.init pivotCount (fun _ -> 
            let randomIndex = random.Next(0, dataset.Length)
            dataset.[randomIndex])

    let createIndex (pivots:Pivots, dataset: NormalizedVector array) : DB = 
        let idx = 
            dataset
            |> Array.map (fun v -> pivots |> Array.map (DistanceFunctions.euclidean v))
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
                printfn $"Early stop at index %i{idx} / %i{lowerBounds.Length}"
                resultsSoFar
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
                | _ -> resultsSoFar


        let acc = new ResultsAccumulator(ComparisonIdentity.FromFunction(fun struct(_,d1) struct(_,d2) -> if d1 < d2 then -1 else 1))
        fillKnnResults 0 acc


[<EntryPoint>]
let main argv =
    let rnd = new Random(2112)
    let vectorSize = 4
    let databaseSize = 10_000
    let pivotCount = 15

    let normalizedDataset = 
        Array.init databaseSize (fun _ -> 
            Array.init vectorSize (fun _ -> rnd.NextDouble()) |> VectorOperations.normalizeVector)

    printfn "Random dataset created"
    printfn "------------------------"

    let pivots = PivotTable.pickPivots normalizedDataset pivotCount
    let db = PivotTable.createIndex (pivots, normalizedDataset)

    printfn "Index  created"
    printfn "------------------------"

    let sampleQueries = Array.init 100 (fun _ -> normalizedDataset[rnd.Next(normalizedDataset.Length)])

    for q in sampleQueries do
        let res = PivotTable.knnQuery (q, db, 10)
        printfn $"ResultCount: {res.Count}, ResultMin : {res.Min}, ResultMax : {res.Max}"

    42
