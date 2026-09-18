# Etapa 6 — Separação de Farey e contagem superior

Referência: o mesmo `paper/main.tex` das etapas anteriores, enviado em
18 de setembro de 2026, SHA-256
`4ac94b1f36e6a48103b25344e8e736657cef2cb5944c600c5afe098119f8b995`.
O manuscrito e as versões de Lean e mathlib não foram alterados.

## Resultado desta etapa

Formalizamos o argumento de separação e a cota superior do Lema 2.1 na
forma por componentes disjuntas usada em sua prova. Para um conjunto
finito S de racionais distintos com denominadores menores que 2Q,
coberto por no máximo R intervalos disjuntos cuja união é E, provamos

```text
#S <= 4 Q^2 |E| + R.
```

Aqui |E| é a medida de Lebesgue, e a versão com valores reais exige
que essa medida seja finita. A versão em reais estendidos também
permite intervalos ilimitados.

São resultados demonstrados sem assumir uma estimativa de contagem.
**São cotas superiores. A oferta de racionais do Lema 2.2, que é uma
cota inferior, continua pendente.**

## Separação aritmética

`FareySeparation.lean` prova inicialmente

```text
1 / (r.den * s.den) <= |r-s|, para r != s.
```

A prova usa o inteiro não nulo
`r.num*s.den - s.num*r.den`, cujo valor absoluto é pelo menos 1.
As frações são elementos de `ℚ`, com numerador e denominador canônicos;
representações repetidas não são contadas como racionais diferentes.

Para denominadores estritamente menores que 2Q, segue a separação
estrita

```text
1 / (4 Q^2) < |r-s|.
```

O limite inferior Q para os denominadores não é necessário nessa
parte. Assim, a estimativa aplica-se em particular ao bloco [Q,2Q)
utilizado no artigo e no restante do projeto.

## Contagem dentro de um intervalo

`card_le_of_separated_values` prova um princípio de empacotamento
para uma família finita de valores reais em [l,u] separados por delta:

```text
card <= (u-l)/delta + 1.
```

A prova envia cada valor x ao natural `floor((x-l)/delta)`. Dois valores
com o mesmo índice estariam a distância menor que delta, contradizendo
a separação. Os índices pertencem a um intervalo finito de naturais.

Tomando delta = 1/(4Q^2), obtemos

```text
card <= 4 Q^2 (u-l) + 1.
```

`sourceFractions_card_le` aplica essa cota ao conjunto exato de fontes
do projeto. `sourceFractions_card_le_one` prova ainda que uma célula de
comprimento até 1/(4Q^2) contém no máximo uma fonte. A igualdade no
comprimento é permitida porque a separação dos racionais é estrita.

## Medida e componentes

`FareyCounting.lean` usa `Set.OrdConnected` para representar intervalos.
Essa condição inclui intervalos abertos, fechados, semiabertos,
degenerados e vazios; não exige escolher um tipo de extremidade único.

Para um conjunto finito não vazio de racionais dentro de um intervalo,
o segmento fechado entre o menor e o maior racional está contido no
intervalo. A monotonicidade da medida permite passar da cota por
comprimento à cota por medida. Para a união, usamos a aditividade da
medida em uma família finita de conjuntos mensuráveis disjuntos e
somamos as cotas de cardinalidade.

As hipóteses de `rational_union_card_le` são:

| Entrada | Condição |
| --- | --- |
| `S` | Conjunto finito de racionais, contados uma única vez |
| `Q` | Natural positivo |
| `t`, `E` | Família finita de conjuntos reais |
| `hR` | A família tem no máximo R membros |
| `hintervals` | Cada membro é um intervalo no sentido de `OrdConnected` |
| `hdisjoint` | Os membros são dois a dois disjuntos |
| `hcover` | Todo racional de S pertence a algum membro |
| `hden` | Cada racional de S tem denominador reduzido menor que 2Q |
| `hfinite` | A união tem medida de Lebesgue finita |

O termo adicional é R, sem fator Q. Isso preserva a característica do
Lema 2.1 necessária no argumento de subníveis da Proposição 5.1.

A decomposição é fornecida como entrada. Esta etapa não implementa um
procedimento que receba intervalos sobrepostos e produza componentes
disjuntas, nem prova a existência e a quantidade de componentes de
um conjunto de subnível analítico. Ela fornece a estimativa a aplicar
quando essa decomposição tiver sido obtida.

## Verificação e pendências

São nove novos teoremas, totalizando 55 teoremas explicitamente
declarados e auditados. Os nomes e suas conexões com o artigo estão
listados no README; a execução dos testes está em `VALIDATION.md`.

A etapa 5 continua fornecendo a construção infinita e a conclusão de
Liouville sob os insumos explícitos de contagem. A presente etapa prova
uma ferramenta usada para obter a cota das fontes perigosas; ela ainda
não fornece `HasUniformDangerBound`.

Continuam pendentes o Lema 2.2, as estimativas analíticas e de
Wronskianos, os argumentos de determinantes e a Proposição 5.1.
Em particular, não se retirou a hipótese `HasSourceSupply` da fusão.
Os Teoremas 1.1 e 1.2 ainda não estão integralmente formalizados.

## Aplicação e commit

Verifique e aplique `MahlerLean-step6.patch` usando `git apply --check`
e `git apply`. Para obter o cache da biblioteca adicional, se necessário:

```bash
lake exe cache get Mathlib.MeasureTheory.Measure.Lebesgue.Basic
```

Em seguida execute `bash scripts/check.sh`. Não execute `lake update`;
as dependências continuam fixadas nas mesmas revisões.

Mensagem sugerida para o commit local:

```text
Prove Farey separation and upper counting on interval components
```

Esta atualização não publica o projeto no GitHub.
