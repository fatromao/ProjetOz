functor
export
    decode:Decode
    executeBlockchain:ExecuteBlockchain
define

    %% STUDENT START:
    
    fun {HashTransaction Tx}
        %% TransitionHash = (nonce + sender + receiver + value) mod 10^6
        (Tx.nonce + Tx.sender + Tx.receiver + Tx.value) mod 1000000
    end

    fun {BlockHash Number PreviousHash Transactions}
        local
            fun {SumHashTransactions Ts}
                case Ts
                of nil then 0
                [] H|T then {HashTransaction H} + {SumHashTransactions T}
                end
            end
        in
        %%BlockHash = (number + previousHash + Σ(i=1 to #transactions) hashTransaction_i) mod 10^6
        (Number + PreviousHash + {SumHashTransactions Transactions}) mod 1000000
        end
    end

    fun {Effort Value}
    %%effort = Σ(i=0 to len(value)-1) 2^i
        if Value < 0 then
            ~1
        else
            local
                fun {LenNb N}
                    if N < 10 then 1
                    else 1 + {LenNb (N div 10)}
                    end
                end
                
                local
                    fun {Pow Base Exp}
                        if Exp == 0 then 1
                        else Base * {Pow Base (Exp - 1)}
                        end
                    end
                in
                    fun {SumEffort N}
                        if N == 0 then 1
                        else {Pow 2 N} + {SumEffort (N - 1)}
                        end
                    end
                end
            in
                {SumEffort ({LenNb Value} - 1)}
            end
        end
    end

    fun {TransactionValidation Transactions Hash Value Balance MaxEffort Block Number PreviousHash}
        %%*le nonce doit être égal au nonce de la dernière transaction envoyée par
        %%cet utilisateur + 1,
        %%*• le hash de la transaction correspond au résultat de la fonction de hachage,
        %%*• le value de la transaction est positif ou nul,
        %%*• le sender a suffisamment de fonds pour effectuer la transaction,
        %%*le max_effort de la transaction est positif,
        %%*• l’effort de la transaction (calculé par la fonction de calcul de l’effort) ne
        %%dépasse pas son max_effort
        local
            local
                fun {Eq H T}
                    if (H - 1) == T then 0
                    else ~1
                    end
                end
            in
                fun {NonceCheck Block}
                    case Block of
                    nil then 0
                    [] H|T then {Eq H T} + {NonceCheck T}
                    end
            if {NonceCheck Transactions} \= 0 then ~1
            elseif (Hash - {BlockHash Number PreviousHash Transactions}) \= 0 then ~1
            elseif Value < 0 then ~1
            elseif Balance < Value then ~1
            elseif MaxEffort <= 0 then ~1
            elseif {Effort Value} > MaxEffort then ~1
            else 0
            end
        end
    end

    fun {BlocValidation BlocNum PreviousBlocNum PreviousHash PreviousBlocHash Hash Number Transactions Value}
        %%*le number du bloc doit être égal au number du bloc précédent + 1,
        %%*• le previousHash du bloc doit être égal au hash du bloc précédent,
        %%*• le hash du bloc doit correspondre au résultat de la fonction de hachage
        %%d’un bloc,
        %%*• toutes les transactions du bloc doivent être valides,
        %%*• la somme des efforts de toutes les transactions du bloc ne doit
        %%pas dépasser l’effort maximal d’un block qui est de 300. Si ajouter
        %%une transaction à un bloc entraîne un dépassement de ce seuil, alors cette
        %%transaction ne doit pas être ajoutée au bloc.
        local
            local
                fun {TransactionValidationAux Transaction}
                    {TransactionValidation Transaction.Block Transaction.Hash Transaction.Number Transaction.PreviousHash Transaction.Transactions Transaction.Balance Transaction.Value Transaction.MaxEffort}
                end
            in
                fun {ValidTrans Transactions}
                    case Transactions of
                    nil then 0
                    [] H|T then {TransactionValidationAux H} + {ValidTrans T}
                    end
                end
            end
            fun {TotalEffort Transactions}
                case Transactions of
                nil then 0
                [] H|T then {Effort H.Value} + {TotalEffort T}
                end
            end
        in
            if BlocNum - 1 \= PreviousBlocNum then ~1
            elseif PreviousHash \= PreviousBlocHash then ~1
            elseif Hash \= {BlockHash Number PreviousHash Transactions} then ~1
            elseif {TotalEffort Transactions} > 300 then ~1
            else 0
            end
        end
    end

    fun {StationValidation AdressX BalanceX NonceX}
        %%• addressX, un entier représentant l’identifiant d’un utilisateur.
        %%• balanceX, un entier représentant le solde de l’utilisateur addressX.
        %%• nonceX, un entier représentant le dernier nonce utiliser par l’utilisateur
        %%addressX.
    end


    %% STUDENT END

    %% Return a string representation of the secret
    fun {Decode Blockchain}
        %% STUDENT START:
        
        %%Pour chaque bloc de la blockchain :
        %%    récupérer le hash du bloc.
        %%    Pour chaque paire de chiffres consécutifs X dans le hash :
        %%        Nombre = X mod 37
        %%        Si Nombre est inférieur à 10 :
        %%            Nombre = 36
        %%        Convertir Nombre en lettre en utilisant le tableau de Sharelock.
        %%        Ajouter tous les caractères obtenus à la phrase secrète.
        %%Retourner la phrase secrète.
        %%Par exemple, si le hash d’un bloc est égal à 284110 :
        %%    28 mod 37 = 28 -> "S"
        %%    51 mod 37 = 14 -> "E"
        %%    10 mod 37 = 10 -> "A"
        %%On obtient donc la phrase secrète "SEA".
        %%Si le hash a un nombre impair de chiffres, le dernier chiffre ne doit pas être pris en compte.
        
        %% STUDENT END
    end


    % This procedure is the starting point of the execution
    % The GenesisState and the Transactions are given as input and the function is expected to bound the FinalState and the FinalBlockchain to their respective final values.
    proc {ExecuteBlockchain GenesisState Transactions FinalState FinalBlockchain}
        %% STUDENT START:
        
        %%• GenesisState, un record représentant l’état initial de la blockchain (comme
        %%expliqué dans la section 2.1.6).
        %%• T ransactions, la liste de toutes les transactions à exécuter (attention, ces
        %%transactions ne contiennent pas l’effort nécessaire pour les exécuter, vous
        %%devez le calculer vous même et l’ajouter à la transaction). Ces transactions
        %%sont triées par ordre de bloc croissant et par ordre dans lequel vous devez
        %%les traiter. Vous pouvez voir cette liste dans le fichier transactions.txt
        %%dans le dossier data du projet.
        %%• F inalState, une variable non initialisée que vous devez assigner à l’état
        %%final de la blockchain après exécution de toutes les transactions.
        %%• F inalBlockchain, une variable non initialisée que vous devez assigner à
        %%la blockchain finale après exécution de toutes les transactions.
        
        %% STUDENT END
    end
end
