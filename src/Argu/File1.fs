#if INTERACTIVE 
#r "System.Xml"
#r "System.Xml.Linq"
#r @"../../bin/net40/argu.dll"
#else
module internal Nessos.Argu.Proposal

#endif

open System.Reflection
open System.Runtime.Serialization.Formatters.Binary
open Microsoft.FSharp.Reflection
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns
open Microsoft.FSharp.Quotations.ExprShape
open Microsoft.FSharp.Quotations.DerivedPatterns
open System
open System.Collections.Generic
open System.Text
open System.Text.RegularExpressions
open Nessos.Argu

[<AutoOpen>]
module Utils =
    open System.IO
    open System.Collections.Generic
    open System.Text
    open System.Reflection

    open System.Xml
    open System.Xml.Linq

    open Microsoft.FSharp.Quotations.Patterns
    let allBindings = BindingFlags.NonPublic ||| BindingFlags.Public ||| BindingFlags.Static ||| BindingFlags.Instance

    /// gets the top-Level methodInfo call in a quotation
    let rec getMethod =
        function
        | Lambda(_,e) -> getMethod e
        | Call(_,f,_) -> f
        | _ -> invalidArg "expr" "quotation is not of method."

    /// reflected version of Unchecked.defaultof
    type Unchecked =
        static member DefaultOf<'T> () = Unchecked.defaultof<'T>
        static member UntypedDefaultOf(t : Type) =
            typeof<Unchecked>
                .GetMethod("DefaultOf", BindingFlags.NonPublic ||| BindingFlags.Static)
                .MakeGenericMethod([| t |])
                .Invoke(null, [||])

    type UnionCaseInfo with
        member uci.GetAttrs<'T when 'T :> Attribute> (?includeDeclaringTypeAttrs) =
            let includeDeclaringTypeAttrs = defaultArg includeDeclaringTypeAttrs false

            let attrs = uci.GetCustomAttributes(typeof<'T>) |> Seq.map (fun o -> o :?> 'T)

            if includeDeclaringTypeAttrs then
                let parentAttrs = uci.DeclaringType.GetCustomAttributes(typeof<'T>, false)  |> Seq.map (fun o -> o :?> 'T)
                Seq.append parentAttrs attrs |> Seq.toList
            else
                Seq.toList attrs

        member uci.ContainsAttr<'T when 'T :> Attribute> (?includeDeclaringTypeAttrs) =
            let includeDeclaringTypeAttrs = defaultArg includeDeclaringTypeAttrs false

            if includeDeclaringTypeAttrs then
                uci.DeclaringType.GetCustomAttributes(typeof<'T>, false) |> Seq.isEmpty |> not
                    || uci.GetCustomAttributes(typeof<'T>) |> Seq.isEmpty |> not
            else
                uci.GetCustomAttributes(typeof<'T>) |> Seq.isEmpty |> not

    [<RequireQualifiedAccess>]
    module List =
        /// fetch last element of a non-empty list
        let rec last xs =
            match xs with
            | [] -> invalidArg "xs" "input list is empty."
            | [x] -> x
            | _ :: rest -> last rest

        /// try fetching last element of a list
        let rec tryLast xs =
            match xs with
            | [] -> None
            | [x] -> Some x
            | _ :: rest -> tryLast rest

        /// <summary>
        ///     returns `Some (map f ts)` iff `(forall t) ((f t).IsSome)`
        /// </summary>
        /// <param name="f"></param>
        /// <param name="ts"></param>
        let tryMap (f : 'T -> 'S option) (ts : 'T list) : 'S list option =
            let rec gather acc rest =
                match rest with
                | [] -> Some <| List.rev acc
                | h :: t ->
                    match f h with
                    | Some s -> gather (s :: acc) t
                    | None -> None

            gather [] ts

        /// Map active pattern combinator
        let (|Map|) f xs = List.map f xs

        /// Nondeterministic Map active pattern combinator
        let (|TryMap|_|) f xs = tryMap f xs


    type ParserCom<'T> = (string -> 'T ) * ('T-> string)

    [<RequireQualifiedAccess>]
    module Boolean =
        let tryParse (inp : string) =
            let ok, b = Boolean.TryParse inp
            if ok then Some b
            else None
            
    type IDictionary<'K,'V> with
        member d.TryFind(k : 'K) =
            let mutable v = Unchecked.defaultof<'V>
            if d.TryGetValue(k, &v) then Some v else None


    /// inherit this type for easy comparison semantics
    type ProjectionComparison<'Id, 'Cmp when 'Cmp : comparison> (token : 'Cmp) =
        member private __.ComparisonToken = token
        interface IComparable with
            member x.CompareTo y =
                match y with
                | :? ProjectionComparison<'Id, 'Cmp> as y -> compare token y.ComparisonToken
                | _ -> invalidArg "y" "invalid comparand."

        override x.Equals y =
            match y with
            | :? ProjectionComparison<'Id, 'Cmp> as y -> token = y.ComparisonToken
            | _ -> false

        override x.GetHashCode() = hash token

    // string monad

    type StringBuilderM = StringBuilder -> unit

    type StringExprBuilder () =
        member __.Zero () : StringBuilderM = ignore
        member __.Yield (txt : string) : StringBuilderM = fun b -> b.Append txt |> ignore
        member __.Yield (c : char) : StringBuilderM = fun b -> b.Append c |> ignore
        member __.YieldFrom f = f : StringBuilderM

        member __.Combine(f : StringBuilderM, g : StringBuilderM) = fun b -> f b; g b
        member __.Delay (f : unit -> StringBuilderM) = fun b -> f () b
        
        member __.For (xs : 'a seq, f : 'a -> StringBuilderM) =
            fun b ->
                let e = xs.GetEnumerator ()
                while e.MoveNext() do f e.Current b

        member __.While (p : unit -> bool, f : StringBuilderM) =
            fun b -> while p () do f b

    let stringB = new StringExprBuilder ()

    [<RequireQualifiedAccess>]
    module String =
        let build (f : StringBuilderM) =
            let b = new StringBuilder ()
            do f b
            b.ToString ()
(*
    Allow Argument Parsing Beyond Primitive Types
    ---------------------------------------------

    Perhaps this could be added via an additional optional parameter for ArgumentParser's constructor
*)
[<AutoOpen>]
module NestingExpr =
    type DeepUnion =
        | Started | From | The | Bottom
        member self.Usage =
            match self with
            | _ -> "it's fucking deep ok?"
        interface  IArgParserTemplate with  member self.Usage = self.Usage

    type SubUnion =
        | Open of int | Close of bool| Exit of byte | Floor of DeepUnion

        member self.Usage =
            match self with
            | Open _ -> "opens it" | Close _ -> "closes it" | Exit _ -> "exits it" | Floor x -> string x

        interface  IArgParserTemplate with  member self.Usage = self.Usage
        

    type ArgUnion =
        | Cmd   of SubUnion
        | Echo  of string
        | Sleep
        | Trick of DeepUnion
        interface  IArgParserTemplate with
            member self.Usage =
                match self with
                | Cmd x  -> x.Usage
                | Echo s -> sprintf "echoes `%s`" s
                | Sleep  -> "goes to sleep"
                | Trick x -> string x



//    let results = parser.Parse([|"--started";"--from";"--open";"--cmd" |])


    open System.Collections.Generic      
    open System    

    let getUnionCaseTree<'union when 'union :> IArgParserTemplate> () =   
        let unionCache = Dictionary<string,UnionCaseInfo>()
        let toplevel = FSharpType.GetUnionCases(typeof<'union>, bindingFlags = allBindings) 
        let rec loop (proc:UnionCaseInfo []) = 
            proc  |> Array.iter (fun caseInfo ->
                if unionCache.ContainsKey caseInfo.Name then () else
                unionCache.Add (caseInfo.Name , caseInfo)
                let nestedTypes = caseInfo.GetFields()
                let subUnions = 
                    nestedTypes |> Array.filter (fun c -> FSharpType.IsUnion c.PropertyType)
                    |> Array.collect (fun u -> FSharpType.GetUnionCases( u.PropertyType, bindingFlags= allBindings))
                match subUnions with
                | [||] -> ()
                | scs  -> loop scs
            )
        loop toplevel
        unionCache |> Seq.map (fun x-> x.Value) |> Array.ofSeq


    let isUnion u = FSharpType.IsUnion u
    let subUnionCases = FSharpType.GetUnionCases(typeof<SubUnion>, bindingFlags = allBindings)
    let argUnionCases = FSharpType.GetUnionCases(typeof<ArgUnion>, bindingFlags = allBindings)


    let cleanTree = getUnionCaseTree<ArgUnion>()

    printfn "cleantree %i" cleanTree.Length




    type  Union = 
        | A | B | C
        override self.ToString () =
            match self with
            | A -> "A"
            | B -> "B"
            | C -> "C"
        static member Parse (s:string) = 
            match s with
            | "a" | "A" -> A
            | "b" | "B" -> B
            | "c" | "C" -> C
            | _ -> failwithf "`%s` could not be parsed into a Union" s

//
//[<AutoOpen>]
//module argkinda =
//
//
//    type ErrorCode =
//        | HelpText = 0
//        | AppSettings = 2
//        | CommandLine = 3
//        | PostProcess = 4
//
//    /// IComparable UnionCaseInfo wrapper
//    type ArgId(uci : UnionCaseInfo) =
//        inherit ProjectionComparison<ArgId,int>(uci.Tag)
//        member __.UCI = uci
//        override __.ToString() = uci.Name
//        
//    /// Represents a parsing schema for a single parameter
//    type ArgInfo =
//        {
//            /// Argument identifier
//            Id : ArgId
//
//            /// Field parser definitions
//            FieldParsers : ParserInfo []
//
//            /// Builds a union case out of its field parameters
//            CaseCtor : obj [] -> obj
//            /// Composes case fields into a tuple, if not nullary
//            FieldCtor : (obj [] -> obj) option
//
//            /// head element denotes primary command line arg
//            CommandLineNames : string list
//            /// name used in AppSettings
//            AppSettingsName : string option
//
//            /// Description of the parameter
//            Usage : string
//
//            /// If specified, should consume remaining tokens from the CLI
//            IsRest : bool
//            /// If specified, parameter can only be at start of CLI parameters
//            IsFirst : bool
//            /// If specified, use '--param=arg' CLI parsing syntax
//            IsEqualsAssignment : bool
//            /// Print labels in Usage ()
//            PrintLabels : bool
//            /// If specified, multiple parameters can be added in AppSettings in CSV form.
//            AppSettingsCSV : bool
//            /// Fails if no argument of this type is specified
//            Mandatory : bool
//            /// Hide from Usage
//            Hidden : bool
//            /// Combine AppSettings with CLI inputs
//            GatherAllSources : bool
//        }
//    with
//        member __.UCI = __.Id.UCI
//        member __.NoCommandLine = __.CommandLineNames.IsEmpty
//
//    and ArgParseResult<'T> =
//        {
//            /// union case value
//            Value : 'T
//
//            /// untyped version of tuple of branch contents
//            FieldContents : obj
//            
//            /// ArgInfo used to parse parameter
//            ArgInfo : ArgInfo
//
//            /// metadata provided by the parser
//            ParseContext : string
//            
//            /// parse source 
//            Source : ParseSource
//        }
//
//    /// Union Case Field info
//    and ParserInfo =
//        {
//            /// Type name
//            Name : string
//            /// field label
//            Label : string option
//            /// field type
//            Type : Type
//            /// parser
//            Parser : string -> obj
//            /// unparser
//            UnParser : obj -> string
//        }
//    with
//        override p.ToString() =
//            match p.Label with
//            | None -> p.Name
//            | Some l -> sprintf "%s:%s" l p.Name
//
//        static member Create (name : string) (parser : string -> 'T) (unparser : 'T -> string) (label : string option) =
//            {
//                Name = name
//                Label = label
//                Type = typeof<'T>
//                Parser = fun x -> parser x :> obj
//                UnParser = fun o -> unparser (o :?> 'T)
//            }
//            
//    exception HelpText
//    exception Bad of string * ErrorCode * ArgInfo option
//
//    let bad code aI fmt = Printf.ksprintf (fun msg -> raise <| Bad(msg, code, aI)) fmt
//
//    /// gets the default name of the argument
//    let getName (aI : ArgInfo) =
//        match aI.CommandLineNames, aI.AppSettingsName with
//        | name :: _, _ -> name
//        | [], Some name -> name
//        | [], None -> failwith "impossible"
//
//    /// checks if given parameter name is contained in argument
//    let hasCommandLineParam (aI : ArgInfo) (param : string) =
//        aI.CommandLineNames |> List.exists ((=) param)
//
//    /// construct a CLI param from UCI name
//    let uciToOpt (uci : UnionCaseInfo) =
//        let prefix = 
//            uci.GetAttrs<CliPrefixAttribute>(true) 
//            |> List.tryPick Some
//            |> Option.map (fun a -> a.Prefix)
//            |> id (fun p -> defaultArg p CliPrefix.DoubleDash)
//
//        let prefixString =
//            match prefix with
//            | CliPrefix.DoubleDash -> "--" 
//            | CliPrefix.Dash -> "-" 
//            | CliPrefix.Empty -> "" 
//            | p -> invalidArg "CliPrefix" <| sprintf "unsupported CLI prefix '%s'." (string p)
//
//        prefixString + uci.Name.ToLower().Replace('_','-')
//
//    /// construct an App.Config param from UCI name
//    let uciToAppConf (uci : UnionCaseInfo) =
//        uci.Name.ToLower().Replace('_',' ')
//
//    /// get CL arguments from environment
//    let getEnvArgs () =
//        match System.Environment.GetCommandLineArgs() with
//        | [||] -> [||]
//        | args -> args.[1..]
//        
//    /// dummy argInfo for --help arg
//    let helpInfo : ArgInfo = 
//        {
//            Id = Unchecked.defaultof<_>
//            CommandLineNames = ["--help" ; "-h" ; "/h" ; "/help" ; "/?"]
//            Usage = "display this list of options."
//            AppSettingsName = None
//            FieldParsers = [||]
//            CaseCtor = fun _ -> invalidOp "internal error: attempting to use '--help' case constructor."
//            FieldCtor = None
//            PrintLabels = false ;
//            Hidden = false ; AppSettingsCSV = false ; Mandatory = false ; 
//            GatherAllSources = false ; IsRest = false ; IsFirst = false
//            IsEqualsAssignment = false
//        }
//
//
//    let primitiveParsers =
//        let mkParser name pars unpars = typeof<'T>, ParserInfo.Create<'T> name pars unpars in
//        dict [
//            mkParser "bool" Boolean.Parse (sprintf "%b")
//            mkParser "byte" Byte.Parse string
//            mkParser "sbyte" SByte.Parse string
//
//            mkParser "int16" Int16.Parse string
//            mkParser "int" Int32.Parse string
//            mkParser "int64" Int64.Parse string
//            mkParser "uint16" UInt16.Parse string
//            mkParser "uint" UInt32.Parse string
//            mkParser "uint64" UInt64.Parse string
//
//            mkParser "char" Char.Parse string
//            mkParser "string" id id
//
//            mkParser "float" Single.Parse string
//            mkParser "float" Double.Parse string
//            mkParser "decimal" Decimal.Parse string
//            mkParser "bigint" System.Numerics.BigInteger.Parse string
//            mkParser "guid" (fun s -> Guid(s)) string
//            mkParser "base64" Convert.FromBase64String Convert.ToBase64String
//        ]
//
//
//    /// recognize exprs that strictly contain DU constructors
//    /// e.g. <@ Case @> is valid but <@ fun x y -> Case y x @> is invalid
//    let expr2ArgId (e : Expr) =
//        let rec aux (tupledArg : Var option) vars (e : Expr) =
//            match tupledArg, e with
//            | None, Lambda(arg, b) -> aux (Some arg) vars b
//            | Some arg, Let(x, TupleGet(Var varg, _), b) when arg = varg -> aux tupledArg (x :: vars) b
//            | None, NewUnionCase(u, []) -> u
//            | Some a, NewUnionCase(u, [Var x]) when a = x -> u
//            | Some _, NewUnionCase(u, List.TryMap (|Var|_|) args) when vars.Length > 0 && List.rev vars = args -> u
//            | _ -> invalidArg "expr" "Only union constructors are permitted in expression based queries."
//
//        ArgId(aux None [] e)
//
//             
//    let preComputeArgInfo' (uci : UnionCaseInfo) : ArgInfo =
//        let fields = uci.GetFields()
//        let types = fields |> Array.map (fun f -> f.PropertyType)
//            
//        let caseCtor = FSharpValue.PreComputeUnionConstructor(uci, bindingFlags = allBindings)
//
//        let dummy = 
//            let dummyFields = types |> Array.map Unchecked.UntypedDefaultOf
//            caseCtor dummyFields :?> IArgParserTemplate
//        
//        let commandLineArgs =
//            if uci.ContainsAttr<NoCommandLineAttribute> (true) then []
//            else
//                let defName = 
//                    match uci.GetAttrs<CustomCommandLineAttribute> () |> List.tryLast with 
//                    | None -> uciToOpt uci
//                    | Some attr -> attr.Name
//
//                let altNames = 
//                    uci.GetAttrs<AltCommandLineAttribute> ()
//                    |> List.map (fun attr -> attr.Name)
//
//                let clNames = defName :: altNames 
//
//                for name in clNames do
//                    if hasCommandLineParam helpInfo name then
//                        failwithf "Argu: parameter '%s' is reserved for the 'usage' parameter." name
//                    let isAllowed = fun c -> Char.IsLetterOrDigit c || c = '-' || c = '/' 
//                    if name.ToCharArray() |> Array.forall isAllowed |> not then
//                        failwithf "Argu: parameter '%s' contains invalid characters." name
//
//                clNames
//
//        let AppSettingsName =
//            if uci.ContainsAttr<NoAppSettingsAttribute> (true) then None
//            else
//                match uci.GetAttrs<CustomAppSettingsAttribute> () |> List.tryLast with
//                | None -> Some <| uciToAppConf uci
//                // take last registered attribute
//                | Some attr -> Some attr.Name
//
//        if AppSettingsName.IsNone && commandLineArgs.IsEmpty then 
//            failwithf "Argu: parameter '%s' needs to have at least one parse source." uci.Name
//
//        let printLabels = uci.ContainsAttr<PrintLabelsAttribute> (true)
//    
//    //    let simpleFields, complexFields = 
//    //        fields |> Array.partition (fun p -> primitiveParsers.ContainsKey( p.PropertyType))
//    //
//    //    //let parsers =
//    //    let simpleParsers =
//    //        let getParser (p : PropertyInfo) =
//    //            let label = if printLabels then Some p.Name else None
//    //            let f = primitiveParsers.[p.PropertyType]
//    //            f label
//    //        Array.map getParser simpleFields
//    //
//    //    let complexParsers =
//    //        let inline mkComplexParser (ptype:^a) = 
//    //            (typeof< ^a>, ParserInfo.Create< ^a> (typeof< ^a>.Name) (fun str -> 
//    //                let conv = Convert.ChangeType(str,typeof< ^a>)
//    //                (^a:(member Parse:string -> ^a) ptype, str)) string)
//    //
//    //        let complexParserDict = System.Collections.Generic.Dictionary<Type,(string option -> ParserInfo)>()        
//    //
//    //        let getParser (p : PropertyInfo) =
//    //            let label = if printLabels then Some p.Name else None
//    //            if complexParserDict.ContainsKey p.PropertyType then
//    //                (complexParserDict.[p.PropertyType]) label
//    //            else
//    //                p.GetValue()
//    //                complexParserDict.Add(mkComplexParser p.PropertyType)
//    //                complexParserDict.[p.PropertyType]
//    ////                | f -> f label
//    ////                | _ -> failwithf "Argu: template contains unsupported field of type '%O'." p.PropertyType
//    //        
//    //        Array.map getParser complexFields
//    //
//    //
//    //
//    //            //| None -> failwithf "Argu: template contains unsupported field of type '%O'." p.PropertyType
//    //
//    //        if complexParsers.ContainsKey p.PropertyType then
//    //            match complexParsers.[p.PropertyType] with
//    //            | f -> f label
//    //            | _ -> failwithf "Argu: template contains unsupported field of type '%O'." p.PropertyType
//    //        else
//    //            let conv = Convert.ChangeType()
//    //
//    //            (mkComplexParser p.PropertyType.) label
//    //
//    //
//
//        (*
//            public object CastPropertyValue(PropertyInfo property, string value) { 
//            if (property == null || String.IsNullOrEmpty(value))
//                return null;
//            if (property.PropertyType.IsEnum)
//            {
//                Type enumType = property.PropertyType;
//                if (Enum.IsDefined(enumType, value))
//                    return Enum.Parse(enumType, value);
//            }
//            if (property.PropertyType == typeof(bool))
//                return value == "1" || value == "true" || value == "on" || value == "checked";
//            else if (property.PropertyType == typeof(Uri))
//                return new Uri(Convert.ToString(value));
//            else
//                return Convert.ChangeType(value, property.PropertyType);  }
//        *)
//
//        let parsers =
//            let getParser (p : PropertyInfo) =
//                let label = if printLabels then Some p.Name else None
//                match primitiveParsers.TryFind p.PropertyType with
//                | Some f -> f label
//                | None -> 
//                    failwithf "Argu: template contains unsupported field of type '%O'." p.PropertyType
//            Array.map getParser fields
//
//
//        let fieldCtor =
//            match types.Length with
//            | 0 -> None
//            | 1 -> Some(fun (o:obj[]) -> o.[0])
//            | _ ->
//                let tupleType = FSharpType.MakeTupleType types
//                let ctor = FSharpValue.PreComputeTupleConstructor tupleType
//                Some ctor
//
//        let AppSettingsCSV = uci.ContainsAttr<ParseCSVAttribute> ()
//        let mandatory = uci.ContainsAttr<MandatoryAttribute> (true)
//        let gatherAll = uci.ContainsAttr<GatherAllSourcesAttribute> ()
//        let isRest = uci.ContainsAttr<RestAttribute> ()
//        let isHidden = uci.ContainsAttr<HiddenAttribute> ()
//        let isEqualsAssignment = 
//            if uci.ContainsAttr<EqualsAssignmentAttribute> (true) then
//                if types.Length <> 1 then
//                    failwithf "Argu: Parameter '%s' has EqualsAssignment attribute but has arity <> 1." uci.Name
//                elif isRest then
//                    failwithf "Argu: Parameter '%s' contains incompatible attributes 'EqualsAssignment' and 'Rest'." uci.Name
//                true
//            else
//                false
//
//        let first = uci.ContainsAttr<FirstAttribute> ()
//
//        if AppSettingsCSV && fields.Length <> 1 then 
//            failwith "Argu: CSV attribute is only compatible with branches of unary fields." 
//
//        {
//            Id = ArgId uci
//            CaseCtor = caseCtor
//            FieldCtor = fieldCtor
//            CommandLineNames = commandLineArgs
//            AppSettingsName = AppSettingsName
//            Usage = dummy.Usage
//            FieldParsers = parsers
//            AppSettingsCSV = AppSettingsCSV
//            Mandatory = mandatory
//            PrintLabels = printLabels
//            GatherAllSources = gatherAll
//            IsRest = isRest
//            IsFirst = first
//            IsEqualsAssignment = isEqualsAssignment
//            Hidden = isHidden
//        }
//
////let conv = Convert.ChangeType(str,typeof< ^a>)
//
//
//let inline mkComplexParser< ^a when ^a:(static member Parse:string -> ^a)>() = 
//    (typeof< ^a>, ParserInfo.Create< ^a> (typeof< ^a>.Name) (fun str -> 
//        (^a:(static member Parse:string -> ^a) str)) string)
//
//let parserDict (psrs:(Type*(string option -> ParserInfo)) seq) = dict psrs
//
//type IDictionary<'k,'v> with
//    member self.ToSeq() = (self :> _ seq) |> Seq.map (fun kvp -> kvp.Key, kvp.Value)
//
//type ComplexParserDict () =
//
//
//
//    
//    let complexParserDict = System.Collections.Generic.Dictionary<Type,(string option -> ParserInfo)>()        
//
//    member inline __.AddParseType<'a when ^a:(static member Parse:string -> ^a)>() =
//        if complexParserDict.ContainsKey (typeof<'a>) then false else
//        complexParserDict.Add (mkComplexParser<'a>())
//        true
//
//    member __.ToDict() =
//       complexParserDict.ToSeq() |>  dict 
//
//
    
//            let getParser (p : PropertyInfo) =
//                let label = if printLabels then Some p.Name else None
//                if complexParserDict.ContainsKey p.PropertyType then
//                    (complexParserDict.[p.PropertyType]) label
//                else
//                    p.GetValue()
//                    complexParserDict.Add(mkComplexParser p.PropertyType)
//                    complexParserDict.[p.PropertyType]
//    //                | f -> f label
//    //                | _ -> failwithf "Argu: template contains unsupported field of type '%O'." p.PropertyType
//            
//            Array.map getParser complexFields
//    
//    
//    
//                //| None -> failwithf "Argu: template contains unsupported field of type '%O'." p.PropertyType
//    
//            if complexParsers.ContainsKey p.PropertyType then
//                match complexParsers.[p.PropertyType] with
//                | f -> f label
//                | _ -> failwithf "Argu: template contains unsupported field of type '%O'." p.PropertyType
//            else
//                let conv = Convert.ChangeType()
//    
//                (mkComplexParser p.PropertyType.) label

//
//    type ArgumentParser' =
//        static member Create<'Template when 'Template :> IArgParserTemplate>(?usageText : string) =
//            new ArgumentParser'<'Template>(?usageText = usageText)
//
//    and ArgumentParser'<'Template when 'Template :> IArgParserTemplate> internal (?usageText : string) =
//        do 
//            if not <| FSharpType.IsUnion(typeof<'Template>, bindingFlags = allBindings) then
//                invalidArg typeof<'Template>.Name "Argu: template type inaccessible or not F# DU."
//
