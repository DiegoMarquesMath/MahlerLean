# Etapa 2 — Da contagem ao centro seguro

Referência: `paper/main.tex` enviado em 18 de setembro de 2026.
SHA-256 do arquivo de referência:
`4ac94b1f36e6a48103b25344e8e736657cef2cb5944c600c5afe098119f8b995`.
O manuscrito não foi alterado nesta etapa.

## Resultado desta etapa

O teorema `MahlerLean.safe_center_of_counting_estimates` formaliza a
**dedução do Lema 6.1 a partir das duas estimativas de contagem**.
As estimativas são parâmetros explícitos do teorema. Ainda não há uma
prova Lean da Proposição 5.1 ou do resultado principal do artigo.

Fixados `f`, `J = [l,u]`, `A`, `M`, `cF`, `Clow` e `C`, com `l < u`
e `cF > 0`, as hipóteses são:

1. **Oferta de racionais (`HasSourceSupply`):** existe um limiar `Qs`
   tal que, para todo `Q >= Qs`, o número de racionais reduzidos de `J`
   com denominador em `[Q,2Q)` é pelo menos `cF (u-l) Q^2`.
2. **Contagem dos centros perigosos (`HasUniformDangerBound`):** existe
   um limiar `Qd`, escolhido antes de `H`, tal que, para todo `H >= 2`
   e todo `Q >= Qd`, o número de centros perigosos é no máximo
   `Clow Q^2 H^(-98) + C Q^(17/10)`.

A conclusão verificada é:

> Existe `Q1 >= 2` tal que, para todo `H >= 2` satisfazendo
> `Clow H^(-98) <= cF (u-l)/4`, e para todo `Q >= Q1`, existe um
> racional reduzido `r` em `J`, com denominador em `[Q,2Q)`, tal que
> `|f(r)-a/b| > 2 b^(-100) + 4 M Q^(-A)` para todo inteiro `a` e
> todo denominador positivo `b` com `H <= b < Q^(A/97)`.

A ordem dos quantificadores preserva a independência de `Q1` em relação
a `H`. O teorema trata um intervalo fixo. Quando formos aplicar isso a
intervalos que encolhem, será necessário fornecer a mesma constante
`Clow` para todos eles, como exige a Proposição 5.1.

O argumento usa `17/10 < 2` para provar, em Lean, que o segundo termo
fica abaixo de um quarto da oferta. Somado ao primeiro quarto, isso
impede que os centros perigosos esgotem o conjunto de candidatos.

## Definições e correspondência com o manuscrito

| Manuscrito | Lean | Convenção |
| --- | --- | --- |
| Racionais fonte de `J`, denominador em `[Q,2Q)` | `sourceFractions l u Q` | Conjunto finito de elementos de `ℚ` |
| Fração reduzida `p/q` | `r.num`, `r.den` | Representação canônica de `ℚ`, com denominador positivo e coprimo ao numerador |
| `T(Q,A)` | `targetCutoff Q A` | Potência real, expoente real `A/97` |
| Margem de segurança | `safetyMargin M Q A b` | Inversos de potências naturais para os expoentes negativos inteiros |
| Testemunha `(a,b)` | `HasTargetWitness` | `a : ℤ`, `b : ℕ`, com `0 < b`; sem coprimalidade no alvo |
| Conjunto perigoso `D(J;Q,A,H)` | `dangerousSources` | Filtra os racionais fonte que admitem alguma testemunha |
| Desigualdade do Lema 6.1 | `IsSafeCenter` | Todos os numeradores e denominadores admissíveis |

O teorema `mem_sourceFractions` prova que a enumeração finita coincide
exatamente com as condições de intervalo e denominador do artigo.
Usar `Finset ℚ` elimina multiplicidades de representações do mesmo
racional. Contam-se centros fonte, e não pares de testemunhas.

Os denominadores positivos são representados por naturais positivos,
equivalentes aos inteiros positivos usados no texto. O parâmetro `A`
é natural; a implicação de contagem para seleção vale para todo `A`.
Na aplicação da Proposição 5.1, será imposto `A >= 3`.

O teorema `safeCenter_avoidance_of_movement` também verifica que todas
as exclusões persistem num ponto `x` quando
`|f(x)-f(r)| <= M Q^(-A)`. A obtenção dessa desigualdade a partir da
cota para a derivada ainda será formalizada.

## O que continua pendente

- Provar a oferta de racionais do Lema 2.2.
- Provar a estimativa da Proposição 5.1 e suas dependências.
- Provar a localização de Wronskianos e o controle dos intervalos.
- Construir a indução completa de fusão (F1)--(F7).
- Identificar o ponto limite como Liouville e provar a exclusão final.
- Deduzir os Teoremas 1.2 e 1.1.

Um teorema condicional provado é uma implicação verificada; suas
hipóteses matemáticas não se tornam resultados demonstrados por isso.
Não foram introduzidos `axiom`, `sorry` ou provas por `native_decide`.

## Arquivos desta atualização

- Novos: `MahlerLean/RationalBlocks.lean`,
  `MahlerLean/CountingToSafeCenter.lean`, `docs/STEP2_PT.md`.
- Atualizados: `MahlerLean.lean`, `scripts/Audit.lean`, `README.md`,
  `VALIDATION.md`, `docs/ROADMAP.md`.
- O texto do artigo e as versões de Lean/mathlib são preservados.

## Conferência e próximo commit

Depois de aplicar a atualização na raiz do projeto:

```bash
bash scripts/check.sh
git diff --stat
git status --short
```

O script compila o projeto, confere cada módulo com avisos tratados como
erros e imprime os axiomas dos 16 teoremas listados. Inspecione essa
saída e os enunciados. O registro do teste realizado está em
`VALIDATION.md`.

Mensagem sugerida para o commit:

```text
Formalize safe-center selection from uniform counting hypotheses
```

O commit é local; esta atualização não cria repositório remoto nem
publica o artigo.
