functor
export
    decode:Decode
    executeBlockchain:ExecuteBlockchain
define
    
    fun {HashTransaction Transaction}
        %% Transaction is a transaction record

        %% TransactionHash = (nonce + sender + receiver + value) mod 10^6
        (Transaction.nonce + Transaction.sender + Transaction.receiver + Transaction.value) mod 1000000
    end

    fun {BlockHash Block}
        %% Block is a block record

        %% BlockHash = (number + previousHash + Σ(i=1 to #transactions) hashTransaction_i) mod 10^6
        local
            fun {SumHashTransactions Ts}
                %% Ts is a transaction list
                case Ts
                of nil then 0
                [] H|T then {HashTransaction H} + {SumHashTransactions T}
                end
            end
        in
        (Block.number + Block.previousHash + {SumHashTransactions Block.transactions}) mod 1000000
        end
    end

    fun {Effort Value}
        %% Value is the value of a transaction

        %% effort = Σ(i=0 to len(value)-1) 2^i
        if Value < 0 then
            ~1
        else
            local
                fun {LengthNb N}
                    if N < 10 then 1
                    else 1 + {LengthNb (N div 10)}
                    end
                end
                fun {SumEffort N}
                    fun {Pow Base Exp}
                        if Exp == 0 then 1
                        else Base * {Pow Base (Exp - 1)}
                        end
                    end
                in
                    if N == 0 then 1
                    else {Pow 2 N} + {SumEffort (N - 1)}
                    end
                end
            in
                {SumEffort ({LengthNb Value} - 1)}
            end
        end
    end

    fun {TransactionValidation Transaction Sender}
        %% Transaction is a transaction record

        %% Sender is a user record with balance and nonce

        %% *• le nonce doit être égal au nonce de la dernière transaction envoyée par cet utilisateur + 1,

        %% *• le hash de la transaction correspond au résultat de la fonction de hachage,

        %% *• le value de la transaction est positif ou nul,

        %% *• le sender a suffisamment de fonds pour effectuer la transaction,

        %% *• le max_effort de la transaction est positif,

        %% *• l’effort de la transaction (calculé par la fonction de calcul de l’effort) ne dépasse pas son max_effort
        local
            fun {NonceCheck Transaction Sender}
                if Transaction.nonce \= (Sender.nonce + 1) then ~1
                else 0
                end
            end

            fun {HashCheck Transaction}
                if {HashTransaction Transaction} \= Transaction.hash then ~1
                else 0
                end
            end
            
            fun {ValueCheck Value}
                if Value < 0 then ~1
                else 0
                end
            end

            fun {BalanceCheck Balance Value}
                if Balance < Value then ~1
                else 0
                end
            end

            fun {MaxEffortCheck MaxEffort}
                if MaxEffort =< 0 then ~1
                else 0
                end
            end

            fun {EffortCheck Value MaxEffort}
                if {Effort Value} > MaxEffort then ~1
                else 0
                end
            end
        in
            if {NonceCheck Transaction Sender} \= 0 then ~1
            elseif {HashCheck Transaction} \= 0 then ~1
            elseif {ValueCheck Transaction.value} \= 0 then ~1
            elseif {BalanceCheck Sender.balance Transaction.value} \= 0 then ~1
            elseif {MaxEffortCheck Transaction.max_effort} \= 0 then ~1
            elseif {EffortCheck Transaction.value Transaction.max_effort} \= 0 then ~1
            else 0
            end
        end
    end


    fun {BlockValidation Block PreviousBlock State}
        %% Block is a block record

        %% PreviousBlock is the previous block record

        %% *• le number du bloc doit être égal au number du bloc précédent + 1,

        %% *• le previousHash du bloc doit être égal au hash du bloc précédent,

        %% *• le hash du bloc doit correspondre au résultat de la fonction de hachage d’un bloc,

        %% *• toutes les transactions du bloc doivent être valides,

        %% *• la somme des efforts de toutes les transactions du bloc ne doit pas dépasser l’effort maximal d’un block qui est de 300. Si ajouter
        %% une transaction à un bloc entraîne un dépassement de ce seuil, alors cette transaction ne doit pas être ajoutée au bloc.
        local
            fun {NumCheck Block PreviousBlock}
                if Block.number \= (PreviousBlock.number + 1) then ~1
                else 0
                end
            end

            fun {PreviousHashCheck Block PreviousBlock}
                if Block.previousHash \= PreviousBlock.hash then ~1
                else 0
                end
            end

            fun {HashCheck Block}
                if Block.hash \= {BlockHash Block} then ~1
                else 0
                end
            end

            fun {TransCheck Transactions State}
                case Transactions of
                nil then State
                [] H|T then
                    Sender = State.(H.sender)
                in
                    if {TransactionValidation H Sender} \= 0 then ~1
                    else
                        SenderNewBalance = Sender.balance - H.value
                        Receiver
                        ReceiverNewBalance
                        StateAfterSender
                        StateAfterReceiver
                    in
                        StateAfterSender = {UpdateState State H.sender SenderNewBalance H.nonce}

                        try
                            Receiver = State.(H.receiver)
                            ReceiverNewBalance = Receiver.balance + H.value
                            StateAfterReceiver = {UpdateState StateAfterSender H.receiver ReceiverNewBalance Receiver.nonce}
                        catch _ then
                            StateAfterReceiver = {UpdateState StateAfterSender H.receiver H.value 0}
                        end

                        {TransCheck T StateAfterReceiver}
                    end
                end
            end

            fun {EffortCheck Transactions}
                local
                    fun {TotalEffort Transactions}
                        case Transactions of
                        nil then 0
                        [] H|T then {Effort H.value} + {TotalEffort T}
                        end
                    end
                in
                    if {TotalEffort Transactions} > 300 then ~1
                    else 0
                    end
                end
            end
        in
            if {NumCheck Block PreviousBlock} \= 0 then ~1
            elseif {PreviousHashCheck Block PreviousBlock} \= 0 then ~1
            elseif {HashCheck Block} \= 0 then ~1
            else
                NewState = {TransCheck Block.transactions State}
            in
                if NewState == ~1 then ~1
                elseif {EffortCheck Block.transactions} \= 0 then ~1
                else 0
                end
            end
        end
    end

    fun {UpdateState State Address Balance Nonce}
        %% State is the current blockchain state

        %% Address is the identifier of the user

        %% Balance is the new balance of the user

        %% Nonce is the new nonce of the user

        %% *• le solde de l’utilisateur doit être mis à jour après une transaction valide,

        %% *• le nonce du sender doit être mis à jour avec le nonce de la transaction exécutée,

        %% *• lorsqu’un utilisateur connu envoie de l’argent à un utilisateur inconnu,

        %% *• ce nouvel utilisateur doit être ajouté au State avec un nonce initial égal à 0,

        %% *• l’ancien State ne doit pas être modifié directement,

        %% *• la fonction doit retourner un nouveau State contenant les informations mises à jour.
        local
            NewUser = user(balance:Balance nonce:Nonce)

            fun {UpdateUsers Users}
                case Users
                of nil then
                    %% User does not exist yet, we add it
                    [Address#NewUser]
                [] A#U|T then
                    if A == Address then
                        %% User exists, we replace it
                        Address#NewUser|T
                    else
                        A#U|{UpdateUsers T}
                    end
                end
            end
        in
            {List.toRecord state {UpdateUsers {Record.toListInd State}}}
        end
    end
    %% STUDENT END

    %% Return a string representation of the secret
    fun {Decode Blockchain}
        %% STUDENT START:
        
        %% Pour chaque bloc de la blockchain :
        %%     récupérer le hash du bloc.
        %%     Pour chaque paire de chiffres consécutifs X dans le hash :
        %%         Nombre = X mod 37
        %%         Si Nombre est inférieur à 10 :
        %%             Nombre = 36
        %%         Convertir Nombre en lettre en utilisant le tableau de Sharelock.
        %%         Ajouter tous les caractères obtenus à la phrase secrète.
        %% Retourner la phrase secrète.
        %% Par exemple, si le hash d’un bloc est égal à 284110 :
        %%     28 mod 37 = 28 -> "S"
        %%     51 mod 37 = 14 -> "E"
        %%     10 mod 37 = 10 -> "A"
        %% On obtient donc la phrase secrète "SEA".
        %% Si le hash a un nombre impair de chiffres, le dernier chiffre ne doit pas être pris en compte.

        local
            fun {Reverse L}
                fun {ReverseAux L Acc}
                    case L 
                    of nil then Acc
                    [] H|T then {ReverseAux T H|Acc}
                    end
                end
            in
                {ReverseAux L nil}
            end

            % Fonction qui transforme un entier en sa liste de chiffres
            fun {IntToDigits N}
                fun {IntToDigitsAux N}
                    if N == 0 then nil
                    else (N mod 10)|{IntToDigitsAux (N div 10)}
                    end
                end
            in
                {Reverse {IntToDigitsAux N}}
            end

            % Fonction qui regroupe les chiffres par paires
            fun {Pairs L}
                case L
                of nil then nil
                [] _|nil then nil
                [] H1|H2|T then (H1 * 10 + H2)|{Pairs T}
                end
            end

            % Fonction qui trouve la lettre correspondante
            fun {NumToLetter N}
                Table = table(10:&a 11:&b 12:&c 13:&d 14:&e 15:&f 16:&g 17:&h 18:&i 19:&j 20:&k 21:&l 22:&m 23:&n 24:&o 25:&p 
                            26:&q 27:&r 28:&s 29:&t 30:&u 31:&v 32:&w 33:&x 34:&y 35:&z 36:& )
                Modulo = N mod 37
            in
                if Modulo < 10 then Table.36
                else Table.Modulo
                end
            end

            %Fonction pour append 2 str
            fun {AppendStr L1 L2}
                case L1
                of nil then L2
                [] H|T then H|{AppendStr T L2}
                end
            end

            % Fonction pour convertir le hash vers un str
            fun{HashToStr Hash}
                fun {PairsToLetters L}
                    case L
                    of nil then nil
                    [] H|T then {NumToLetter H}|{PairsToLetters T}
                    end
                end
            in
                {PairsToLetters {Pairs {IntToDigits Hash}}}
            end


        in
            case Blockchain
            of nil then nil
            [] H|T then {AppendStr {HashToStr H.hash} {Decode T}}
            end
        end 
    end


    %% This procedure is the starting point of the execution
    %% The GenesisState and the Transactions are given as input and the function is expected to bound the FinalState and the FinalBlockchain to their
    %% respective final values.
    proc {ExecuteBlockchain GenesisState Transactions FinalState FinalBlockchain}
        %% STUDENT START:
        
        %% *• GenesisState, un record représentant l’état initial de la blockchain (comme expliqué dans la section 2.1.6).

        %% *• Transactions, la liste de toutes les transactions à exécuter (attention, ces transactions ne contiennent pas l’effort nécessaire pour les
        %% exécuter, vous devez le calculer vous même et l’ajouter à la transaction). Ces transactions sont triées par ordre de bloc croissant et par ordre
        %% dans lequel vous devez les traiter. Vous pouvez voir cette liste dans le fichier transactions.txt dans le dossier data du projet.

        %% *• FinalState, une variable non initialisée que vous devez assigner à l’état final de la blockchain après exécution de toutes les transactions.

        %% *• FinalBlockchain, une variable non initialisée que vous devez assigner à la blockchain finale après exécution de toutes les transactions.
        
        fun {GenesisToStateLocal GenesisState}
            %% GenesisState is a genesis record

            %% Returns the initial blockchain state
            local
                fun {UsersToState Users}
                    case Users
                    of nil then nil
                    [] Address#Balance|T then
                        Address#user(balance:Balance nonce:0)|{UsersToState T}
                    end
                end
            in
                {List.toRecord state {UsersToState {Record.toListInd GenesisState}}}
            end
        end

        fun {AppendList L X}
            case L of
            nil then [X]
            [] H|T then H|{AppendList T X}
            end
        end

        fun {MakeBlock Number PreviousHash Transactions}
            TempBlock
            TempHash
        in
            TempBlock = block(
                number:Number
                previousHash:PreviousHash
                transactions:Transactions
                hash:0
            )

            TempHash = {BlockHash TempBlock}

            block(
                number:Number
                previousHash:PreviousHash
                transactions:Transactions
                hash:TempHash
            )
        end

        fun {ApplyTransaction Transaction State}
            Sender = State.(Transaction.sender)
            UpdateWithSender
            UpdateWithReceiver
        in
            UpdateWithSender =
                {UpdateState State Transaction.sender (Sender.balance - Transaction.value) Transaction.nonce}

            try
                Receiver = UpdateWithSender.(Transaction.receiver)
            in
                UpdateWithReceiver =
                    {UpdateState UpdateWithSender Transaction.receiver (Receiver.balance + Transaction.value) Receiver.nonce}
            catch _ then
                UpdateWithReceiver =
                    {UpdateState UpdateWithSender Transaction.receiver Transaction.value 0}
            end

            UpdateWithReceiver
        end

        fun {TryAddTransaction Transaction State CurrentTransactions CurrentEffort}
            try
                Sender = State.(Transaction.sender)
            in
                if {TransactionValidation Transaction Sender} \= 0 then
                    result(state:State transactions:CurrentTransactions effort:CurrentEffort)
                elseif CurrentEffort + {Effort Transaction.value} > 300 then
                    result(state:State transactions:CurrentTransactions effort:CurrentEffort)
                else
                    NewState = {ApplyTransaction Transaction State}
                    NewTransactions = {AppendList CurrentTransactions Transaction}
                    NewEffort = CurrentEffort + {Effort Transaction.value}
                in
                    result(state:NewState transactions:NewTransactions effort:NewEffort)
                end
            catch _ then
                result(state:State transactions:CurrentTransactions effort:CurrentEffort)
            end
        end

        fun {Process Transactions State Blockchain PreviousBlock CurrentBlockNumber CurrentTransactions CurrentEffort}
            case Transactions of
            nil then
                if CurrentBlockNumber == ~1 then
                    result(state:State blockchain:Blockchain)
                else
                    FinalBlock = {MakeBlock CurrentBlockNumber PreviousBlock.hash CurrentTransactions}
                    NewBlockchain = {AppendList Blockchain FinalBlock}
                in
                    result(state:State blockchain:NewBlockchain)
                end

            [] H|T then
                if CurrentBlockNumber == ~1 then
                    {Process Transactions State Blockchain PreviousBlock H.block_number nil 0}

                elseif H.block_number \= CurrentBlockNumber then
                    FinalBlock = {MakeBlock CurrentBlockNumber PreviousBlock.hash CurrentTransactions}
                    NewBlockchain = {AppendList Blockchain FinalBlock}
                in
                    {Process Transactions State NewBlockchain FinalBlock H.block_number nil 0}

                else
                    R = {TryAddTransaction H State CurrentTransactions CurrentEffort}
                in
                    {Process T R.state Blockchain PreviousBlock CurrentBlockNumber R.transactions R.effort}
                end
            end
        end

        InitialState = {GenesisToStateLocal GenesisState}
        GenesisBlock = block(number:~1 previousHash:0 transactions:nil hash:0)
        Result = {Process Transactions InitialState nil GenesisBlock ~1 nil 0}
    in
        FinalState = Result.state
        FinalBlockchain = Result.blockchain
    end
end