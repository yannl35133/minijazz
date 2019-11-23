Compilation
===========

Pour compiler MiniJazz, utilisez la commande suivante:

```
ocamlbuild mjc.byte
```

Utilisation
===========

Il suffit de lancer le compilateur en lui donnant un fichier `.mj`:

```
./mjc.byte test/nadder.mj
```

Cela génère un fichier `test/nadder.net` contenant une net-list non 
ordonnée.

Pour obtenir les options du compilateur, utilisez l'option `-h`:

```
./mjc.byte -h
```

Une option importante est `-m` qui doit être suivi du nom du bloc principal 
du circuit. Par défaut, le compilateur recherche un bloc appelé *main*.

Pour la description du langage MiniJazz et du langage de net-list, voir le 
sujet du TP1 du cours L3 de *systèmes numériques* à l'ENS.

Modifications
=======

Cette version est modifiée afin de tirer partie des simulateurs de netlist
permettant l'application des opérations aux nappes.

Les opérateurs `or`,`and`,`xor` et `not` peuvent êtres utilisés sur des nappes:

```
o1 = n_or<4>(a,b)
```

`reg` peut être utilisé sur des nappes avec la même syntaxe que pour les fils.

Voir [n_ops](./test/n_ops.mj).

Crédits
=======

Le langage Jazz a été conçu par [Jean Vuillemin](https://www.di.ens.fr/~jv/).

Le compilateur MiniJazz a été développé par Cédric Pasteur (certaines 
parties ont été supprimées de cette version accessible au public).

N'hésitez pas à faire des « Pull Requests » pour corriger des bogues ou 
proposer des améliorations. Merci de ne pas partager les solutions aux 
exercices.

