# Etapa 9 — parâmetros do regime large-target

Esta etapa formaliza as desigualdades numéricas usadas no regime
large-target da Proposition 5.1.

O módulo principal é:

`MahlerLean/LargeTargetParameters.lean`

Para `u >= 1/5`, definem-se

- `d = ceil(10u)`;
- `N = 2(d+1)`;
- `kappa = 3(d+u)/(N-1)`;
- `s = min(100u,A)`.

A formalização prova, entre outras estimativas,

- `d >= 2`;
- `d <= D(A)`;
- `kappa <= 33/20`;
- `kappa N <= 96u`;
- `s >= 97u`;
- `s - kappa N >= 1/5`;
- `s/(N-1) >= 97/35 > 2`.

O principal resultado agregador é

`largeTargetParameterBundle`.

Ele reúne exatamente as desigualdades numéricas necessárias para o
regime large-target da Proposition 5.1.

Esta etapa não formaliza ainda os determinantes, o lema de subnível ou
a Proposition 5.1 completa. Nenhum resultado pendente é introduzido
como axioma ou placeholder.
