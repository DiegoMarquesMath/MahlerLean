# Etapa 3 — Conclusão da fusão a partir dos invariantes

Referência: o mesmo `paper/main.tex` da etapa 2, enviado em 18 de setembro
de 2026, SHA-256
`4ac94b1f36e6a48103b25344e8e736657cef2cb5944c600c5afe098119f8b995`.
O manuscrito não foi alterado.

## O que esta etapa prova

Esta atualização verifica a conclusão da construção de fusão da Seção 6.
**A existência da sequência de intervalos e de seus invariantes ainda é
uma hipótese explícita.** A estrutura `FusionData f` reúne esses dados;
ela não afirma que eles existem para uma função analítica qualquer.

O teorema `exists_escape_of_fusion_data` prova que tais dados produzem
um ponto `x` que:

- pertence a todos os intervalos;
- é Liouville na definição da mathlib;
- é Liouville na definição do manuscrito, com infinitos pares para cada
  expoente e erro estritamente positivo;
- satisfaz `|f(x)-a/b| > b^(-100)` para todo inteiro `a` e todo natural
  `b >= T_0`, com `T_0 >= 2`;
- tem imagem que não é Liouville.

A cota explícita de aproximação é a conclusão quantitativa usada no
artigo. Esta atualização não introduz uma definição de `mu` nem prova
um teorema Lean formulado diretamente como `mu(f(x)) <= 100`.

## Hipóteses exatas de FusionData

| Campo | Conteúdo matemático |
| --- | --- |
| `left`, `right`, `interval_nonempty` | Intervalos fechados não vazios `I_n = [l_n,u_n]` |
| `nested` | `I_(n+1)` contido em `I_n` |
| `center`, `center_den` | Centros racionais reduzidos `r_n`, com denominador pelo menos 2 |
| `cutoff`, `cutoff_start`, `cutoff_strict` | Cortes naturais `T_n`, estritamente crescentes, com `T_0 >= 2` |
| `source_approx` | Para todo `x` em `I_(n+1)`, `0 < |x-r_n| < q_n^(-(n+3))` |
| `target_avoid` | Para todo `x` em `I_(n+1)`, exclusão dos alvos com `T_n <= b < T_(n+1)` |

São os invariantes necessários à conclusão da fusão. A inclusão em
interiores, os Wronskianos e o controle do próximo corte são necessários
para construir os dados no artigo, mas não são pressupostos adicionais
para deduzir a conclusão depois de receber esses dados.

A compacidade e a inclusão dos intervalos dão um ponto na interseção.
A prova de existência não precisa estabelecer primeiro a unicidade do
ponto. A unicidade e o encolhimento dos diâmetros não são resultados
formalizados nesta atualização.

## Compatibilidade da definição de Liouville

`PaperLiouville x` declara que, para cada natural `N >= 1`, o conjunto

```text
{(a,b) : integer x natural |
  b >= 2 and 0 < |x-a/b| and |x-a/b| < 1/b^N}
```

é infinito. A equivalência `liouville_iff_paperLiouville` é provada nas
duas direções. Na direção da definição da biblioteca para a do artigo,
usamos a existência de aproximações com denominadores arbitrariamente
grandes, já demonstrada na mathlib. Não se conta uma aproximação exata
como aproximação de Liouville.

A condição de aproximação fonte é aplicada com `A_n = n+3`. Isso fornece
todos os expoentes exigidos por `Liouville`; a equivalência acima dá a
convenção de infinitos pares adotada no artigo.

## Cobertura dos alvos e controle pela derivada

`exists_target_block` prova que qualquer natural `b >= T_0` pertence a
algum bloco `[T_n,T_(n+1))`. O teorema `target_avoidance_from_blocks`
transforma as exclusões nesses blocos na cota eventual para todos os
alvos. Essa cota contradiz a propriedade de Liouville da imagem.

O teorema `safeCenter_avoidance_of_deriv_bound` também fecha uma etapa
local deixada explícita na atualização anterior. Sob diferenciabilidade
no intervalo, cota `|f'| <= M` e `|x-r| <= Q^(-A)`, o teorema do valor
médio fornece `|f(x)-f(r)| <= M Q^(-A)`. A segurança do centro então
implica a exclusão dos alvos no ponto próximo `x`.

## Novos teoremas

1. `liouville_iff_paperLiouville`.
2. `liouville_of_source_approximations`.
3. `not_liouville_of_eventual_target_avoidance`.
4. `exists_target_block`.
5. `target_avoidance_from_blocks`.
6. `exists_escape_of_fusion_data`.
7. `safeCenter_avoidance_of_deriv_bound`.

Todos têm entradas em `scripts/Audit.lean`. O projeto agora possui 23
teoremas explicitamente declarados e listados na auditoria.

## O que falta para o resultado principal

A tarefa central restante na fusão é construir `FusionData f` a partir
dos centros seguros, preservando simultaneamente as condições (F1)--(F7).
Isso inclui remover os zeros dos Wronskianos e o centro atual, obter um
intervalo de comprimento controlado e verificar a condição para o próximo
corte inferior. As provas da oferta de racionais e da Proposição 5.1,
com suas dependências, também continuam pendentes.

Ainda não é correto descrever o Teorema 1.2 ou a construção completa de
fusão como formalizados. Há duas implicações verificadas: das estimativas
para a seleção do centro, e dos invariantes construídos para o ponto de
escape. Falta construir e conectar os dados que satisfazem as hipóteses.

## Próximo commit

Depois de aplicar a atualização, execute `bash scripts/check.sh`.
A mensagem sugerida é:

```text
Formalize the conclusion of fusion from explicit invariants
```

O commit continua local. Nenhuma publicação no GitHub é feita por esta
atualização.
