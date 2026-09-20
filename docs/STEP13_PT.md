# Etapa 13: do determinante à contagem uniforme

Esta etapa formaliza o núcleo do método do determinante usado na
Proposição 5.1. Ela ainda não declara a proposição completa: faltam a montagem
simultânea das células e escalas e a soma final dos blocos de alturas-alvo.

## Resultados verificados

1. `targetLinearMatrix_det_lower_dyadic` mantém separadas as alturas da fonte
   e do alvo ao limpar denominadores.
2. `exists_targetLinearMatrix_analytic_upper_bound` controla o determinante
   por
   `K * (rho^(N*(N-1)/2) + delta)`.
3. `exists_targetLinearMatrix_det_zero_of_clustered_approximations` compara
   os limites analítico e aritmético e força o determinante a ser zero.
4. `exists_unit_relation_of_all_det_zero` prova o passo abstrato de posto:
   se todos os menores máximos se anulam, existe uma relação comum com
   vetor de coeficientes de norma um.
5. `exists_unit_targetLinear_graph_sublevel_of_all_det_zero` transfere a
   relação exata nos valores racionais aproximantes para uma relação pequena
   no gráfico analítico.
6. `exists_uniform_analytic_sublevel_disjoint_interval_cover` produz uma
   união exata de intervalos dois a dois disjuntos, com número uniformemente
   limitado.
7. `exists_targetLinear_counting_bound_of_all_det_zero` combina a relação, o
   limite uniforme de subnível e a separação de Farey numa estimativa de
   contagem para qualquer conjunto racional finito que satisfaça as hipóteses
   de anulação.

Todos esses resultados são compilados com `-DwarningAsError=true` e entram na
auditoria de axiomas. As únicas dependências lógicas impressas são as usuais
da biblioteca (`propext`, `Classical.choice` e `Quot.sound`).

## Próximo bloco

O próximo passo deve construir, a partir dos testemunhos racionais da
Proposição 5.1, a família finita à qual o teorema de contagem acima se aplica:

- escolher uma aproximação-alvo por centro;
- verificar a anulação para toda seleção de `N = 2(d+1)` centros na mesma
  célula;
- inserir as escolhas de `d`, `rho`, `delta`, `Q` e `H` já controladas pelos
  lemas de parâmetros grandes;
- somar os blocos de alturas-alvo preservando a perda de expoente prevista no
  artigo.

Somente depois dessa montagem o projeto poderá afirmar a Proposição 5.1 na
forma usada pela construção de fusão.

## Montagem das somas e pendência do determinante

`CellCountingAssembly.lean` formaliza a soma das contagens sobre uma
cobertura finita (sem hipótese de disjunção), a multiplicação de uma cota
uniforme por célula pelo número de células e a absorção eventual
`log Q * Q^(33/20) ≤ Q^(17/10)`.
Esses lemas ainda não constroem as células nem contam os blocos diádicos.

O enunciado em `paper/main.tex` pede o expoente `17/10`, com constantes
independentes de H. A montagem deve seguir esse enunciado.

Há uma pendência anterior à montagem final: a cota atualmente formalizada
em `TargetLinearDeterminantUpper.lean` tem a forma
`K * (rho^(N*(N-1)/2) + delta)`. O artigo utiliza a estimativa perturbada
mais forte, preservando a potência do comprimento da célula quando
`delta ≤ rho^N`. A cota aditiva existente não fornece automaticamente
esse resultado. Por exemplo, para u=10, d=100, N=202 e A=1000, a
escala aritmética tem expoente N(d+u)=22220, enquanto s=min(100u,A)=1000.
Assim, o termo aditivo de erro não é pequeno o suficiente para a comparação
assintótica nessa escolha. Isso identifica uma lacuna na formalização,
não uma refutação do lema perturbado do artigo.

A continuação abaixo prova a versão forte com base fixa. A uniformidade
na posição das células permanece necessária.

## Expansão multilinear e limiar uniforme

A origem exata da perda foi identificada em
`abs_det_add_le_of_remainder_rows`: após selecionar uma linha pequena,
as demais são estimadas individualmente por B, perdendo o decaimento
conjunto dos vetores da curva.

A nova rota preserva essa informação sem exigir Wronskianos não nulos:

- `SmoothCurveMinorDecay.lean` prova o decaimento triangular para os menores
de m linhas da curva, uniformemente nas escolhas de coordenadas, incluindo
m=0 e m=1.
- `MixedDeterminantDecay.lean` usa expansão de Laplace pelas linhas de erro
para obter os fatores delta^r e rho^((N-r)(N-r-1)/2). A prova combina esses
fatores na expansão multilinear já existente. Os fatores combinatórios
são absorvidos numa constante finita.
- `exists_smooth_curve_perturbed_sum_bound` estabelece a versão matricial
de (4.8) para pontos próximos de uma base de Taylor fixa.
- `exists_targetLinearMatrix_strong_perturbed_bound` dá o corolário forte
para a curva alvo-linear sob delta ≤ rho^N, sem hipótese sobre Wronskianos.
- `MultilinearPerturbation.lean` prova (4.9), a absorção dos termos da soma
e `largeTarget_vertical_error_le_radius_power`, que liga diretamente
s-kappa*N ≥ 1/5 ao limiar Q ≥ K0^5. Esse limiar não depende de u, B ou H.

Os novos arquivos foram compilados com warningAsError=true e os resultados
principais auditados: somente propext, Classical.choice e Quot.sound.

Limite preciso: as constantes analíticas acima ainda são escolhidas para
um intervalo e sua extremidade esquerda fixos. Para concluir o lema do
artigo em toda célula móvel dentro de J, falta extrair os limites de
Taylor/derivadas uniformemente na base em J. Só depois essa estimativa
substituirá a interface usada na montagem global da Proposição 5.1.
A alternativa por inversão da matriz de derivadas não foi incorporada.
