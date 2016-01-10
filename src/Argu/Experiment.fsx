#I "../../bin/net40"
#r "Argu.dll"

open System
open System.Collections.Generic
open Nessos.Argu

type BOOM (str) =
    override __.ToString() = str
    static member Parse str =
        match str:string with
        | "boom" | "Boom" -> BOOM str
        | "BOOM" -> BOOM "GOES THE DYNAMITE"
        | _      -> failwith "can't go BOOM"

type POW (str) =
    override __.ToString() = str
    static member Parse str =
        match str:string with
        | "pow" | "Pow" | "POW" -> POW str
        | "explode" -> POW "MUSIC MAKES YOU LOSE CONTROL"
        | _     -> failwith "got no POW"


type Tri =
    | A | B | C
    static member Parse str =
        match str:string with
        | "A" | "a" | "aye" | "ei" -> A
        | "b"|"B"|"bee"-> B
        | "c"|"C"|"sea"|"SEA"-> C
        | _ -> failwith "failure"

let trickyDict = 
    parserDict [ 
        mkComplexParser<BOOM>() 
        mkComplexParser<POW> () 
        mkComplexParser<Tri> ()
    ]

type CLIArguments =
    | Listener of host:string * port:int
    | Detach | Boom of BOOM | Pow of POW 
    | Three of Tri
with 
    interface IArgParserTemplate with
        member s.Usage =
            match s with
            | Listener _ -> "specify a listener (hostname : port)."
            | Detach _   -> "detach daemon from console."
            | Boom _     -> "when I say boom"
            | Pow _      -> "you say pow"
            | Three _    -> "Nested DU baby"

let parser  = ArgumentParser.Create<CLIArguments>(parserDict=trickyDict)
let usage   = parser.Usage() |> printfn "%A"
let results = 
    parser.Parse([| "--detach" ; "--listener" ; "localhost" ; "8080"; 
                    "--pow";"explode";"--boom";"BOOM";
                    "--three";"SEA"
                |]);;

results.GetAllResults() |> List.iter (printfn "%A")
printfn "%A" <| results.Contains <@ Boom @>;;
(*
    > Listener ("localhost",8080)
    Detach
    Boom GOES THE DYNAMITE
    Pow MUSIC MAKES YOU LOSE CONTROL
    true
*)

let results' = parser.Parse([| "--detach" ; "--listener" ; "localhost" ; "8080"; "--pow";"pow";"--boom";"boom"|])
results'.GetAllResults() |> List.iter (printfn "%A");;
(*
    >
    Listener ("localhost",8080)
    Detach
    Boom boom
    Pow pow
*)

// To add this functionality I changed `preComputeArgInfo` to:
