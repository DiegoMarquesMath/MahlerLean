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
   se todos os menores máximos se anulam, existe uma única relação comum com
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
