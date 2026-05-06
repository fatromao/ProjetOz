functor
export
    decode:Decode
    executeBlockchain:ExecuteBlockchain
define

    %% STUDENT START:
    
    fun {TransitionHash Nonce Sender Receiver Value}
        %%TransitionHash = (nonce + sender + receiver + value) mod 10^6
    end

    fun {BlockHash Number PreviousHash TransactionsNum HashTransaction}
        %%BlockHash = (number + previousHash + Σ(i=1 to #transactions) hashTransaction_i) mod 10^6
    end

    fun {Effort Value}
        %%effort = Σ(i=0 to len(value)-1) 2^i
    end

    fun {TransactionValidation Nonce Hash Sender Value MaxEffort Effort}
        %%le nonce doit être égal au nonce de la dernière transaction envoyée par
        %%cet utilisateur + 1,
        %%• le hash de la transaction correspond au résultat de la fonction de hachage,
        %%• le sender a suffisamment de fonds pour effectuer la transaction,
        %%• le value de la transaction est positif ou nul,
        %%le max_effort de la transaction est positif,
        %%• l’effort de la transaction (calculé par la fonction de calcul de l’effort) ne
        %%dépasse pas son max_effort
    end

    fun {BlocValidation BlocNum PreviousHash Hash Bloc MaxEffort}
        %%le number du bloc doit être égal au number du bloc précédent + 1,
        %%• le previousHash du bloc doit être égal au hash du bloc précédent,
        %%• le hash du bloc doit correspondre au résultat de la fonction de hachage
        %%d’un bloc,
        %%• toutes les transactions du bloc doivent être valides,
        %%• la somme des efforts de toutes les transactions du bloc ne doit
        %%pas dépasser l’effort maximal d’un block qui est de 300. Si ajouter
        %%une transaction à un bloc entraîne un dépassement de ce seuil, alors cette
        %%transaction ne doit pas être ajoutée au bloc.
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
