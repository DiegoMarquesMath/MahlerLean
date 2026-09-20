# Etapa 12 — subníveis uniformes de famílias analíticas

## Resultado

O teorema `exists_uniform_analytic_sublevel_bound` reúne a estimativa de
medida e a representação como união finita de intervalos. Para uma família
analítica de N funções, N ≥ 2, cujo Wronskiano não se anula no intervalo
compacto J, existem C > 0, R > 0 e 0 < ε₀ < 1 tais que, simultaneamente
para todo vetor de coeficientes de norma euclidiana 1 e todo 0 ≤ ε < ε₀:

- o subnível de |G_c| é exatamente uma união de no máximo R intervalos;
- sua medida é no máximo C ε^(1/(N−1)).

Os intervalos são conjuntos `OrdConnected`; podem ser vazios, degenerados
ou sobrepostos. A igualdade com a união é expressa por uma equivalência
de pertinência para todo ponto, não apenas por uma inclusão.

O teorema `exists_uniform_rational_relation_sublevel_bound` especializa
esse resultado à família x^i f(x)^j, com 0 ≤ i ≤ d e j = 0,1. Os
coeficientes estão na ordem (0,0),(0,1),…,(d,1), com norma euclidiana 1,
e a conclusão usa explicitamente a soma desses monômios. N = 2(d+1).
As constantes são escolhidas antes dos coeficientes e de ε.

## Estrutura da prova

1. `AnalyticLinearCombination`: identifica derivadas e coordenadas do jato.
2. `LocalJetPersistence`, `FiniteJetCover`, `UniformIntervalCover`: extraem
   por compactidade uma cobertura finita uniforme em coeficientes e fonte.
3. `LocalUniformSublevel`, `FiniteSublevelAssembly`, `UniformSublevelGlobal`:
   provam a cota global de medida, incluindo o caso de ordem zero.
4. `SublevelIntervals`: corta um intervalo num conjunto finito de pontos
   onde |g| = ε. Inclui pontos isolados e produz no máximo 2#B+1 peças.
   A cota #B ≤ 2k, já provada por Rolle, fornece 4k+1 peças.
5. `UniformSublevelIntervals`: aplica essa decomposição em cada intervalo
   da cobertura e recorta a união pelo intervalo-fonte J.
6. `UniformSublevel`: reúne medida e intervalos com constantes positivas
   e fornece a especialização racional.

## Escopo e limites

Esta etapa formaliza o caso **analítico** do Lemma 3.5 necessário à
aplicação racional do Corollary 3.6. O enunciado mais geral do manuscrito,
para famílias apenas C^(N−1), não é afirmado por esses teoremas.

A cota local de número de peças é 4k+1, em vez de 2k+1; ambas fornecem a
constante uniforme existencial exigida na aplicação. Não se reivindica
que as peças construídas sejam as componentes conexas maximais ou que
sejam disjuntas. A interface de contagem de Farey que exige uma família
disjunta ainda precisa de uma decomposição compatível ou de um adaptador.

A não anulação do Wronskiano é hipótese explícita. Ainda faltam a dedução
dessa propriedade a partir da não racionalidade, os determinantes, a
Proposição 5.1 e a integração final ao Teorema 1.2. Nenhuma dessas partes
é instalada como axioma ou placeholder.
