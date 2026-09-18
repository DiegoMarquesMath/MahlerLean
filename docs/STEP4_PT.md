# Etapa 4 — Uma etapa da construção de fusão

Referência: o mesmo `paper/main.tex` das etapas anteriores, enviado em
18 de setembro de 2026, SHA-256
`4ac94b1f36e6a48103b25344e8e736657cef2cb5944c600c5afe098119f8b995`.
O manuscrito e as versões de Lean e mathlib não foram alterados.

## Resultado desta atualização

O teorema `successor_from_counting` constrói **uma etapa** da fusão da
Seção 6. Dados um intervalo pai, um corte inferior H e um conjunto finito
Z a evitar, ele escolhe Q, um centro racional seguro r e um intervalo
filho de comprimento positivo. A hipótese de contagem, a oferta de
racionais e as condições locais de derivada e de cauda são explícitas.

O resultado não pressupõe a existência do intervalo filho: ela é provada.
Ainda não se constrói a sequência infinita `FusionData f` nem se provam
as hipóteses analíticas do artigo.

## Geometria e pontos proibidos

`FiniteAvoidance.lean` prova que, se um conjunto F tem menos de N pontos,
o intervalo aberto (a,b) contém um intervalo fechado de comprimento
(b-a)/(2N) que não encontra F. A prova usa N intervalos fechados separados:
se todos encontrassem F, haveria pelo menos N pontos distintos em F.

Aplicamos isso com F = Z unido ao centro r, N = #Z+2 e (a,b) = (r-R,r+R).
O intervalo obtido tem comprimento exatamente R/(#Z+2), evita Z e r,
e satisfaz 0 < |x-r| < R em todos os seus pontos. Se r está no terço
médio do pai e R é menor que um terço do comprimento do pai, o intervalo
filho está contido no interior do pai.

É uma prova alternativa ao argumento por componentes conexas do artigo,
com a mesma constante e o mesmo comprimento. Nesta etapa Z é um conjunto
finito arbitrário; não se demonstrou ainda que ele pode ser escolhido
como o conjunto de zeros dos Wronskianos pertinentes.

## Corte inteiro e condição de cauda

`FusionScale.lean` usa as definições

```text
X = targetCutoff Q A = Q^(A/97)
R = fusionRadius Q A = (2Q)^(-A)
T_next = nextCutoff Q A = floor(X)
Lambda = #Z + 2.
```

Para X >= 2, provamos X/2 <= T_next <= X. A condição (Q3),
2H+2 <= X, dá H < T_next. A identidade X^97 = Q^A e a estimativa
T_next^(-98) <= 2^98 X^(-98) permitem provar que (Q4),

```text
3 Clow Lambda 2^(A+98) X^(-1) <= cF/4,
```

implica

```text
Clow T_next^(-98) <= (cF/4) * (R/(3 Lambda)).
```

Como o terço médio do filho tem comprimento R/(3 Lambda), essa é a
condição de cauda (F7) necessária para aplicar novamente a seleção do
centro. Não se perde a constante uniforme Clow ao reduzir o intervalo.

`exists_large_fusion_scale` prova que, para A > 0, cF > 0 e uma margem
positiva, há Q acima de qualquer mínimo prescrito que satisfaz ao mesmo
tempo a condição de encaixe de R, (Q3) e (Q4). A prova usa limites da
mathlib. Todos os parâmetros, inclusive Lambda, são fixados antes de Q.

## Ligação com a seleção do centro

`FusionStep.lean` contém dois teoremas:

- `successor_from_safe_center` constrói o intervalo filho depois de Q e
  r estarem disponíveis e satisfazerem as condições locais.
- `successor_from_counting` obtém também Q e r a partir da oferta de
  racionais e da estimativa uniforme de fontes perigosas no terço médio.

No segundo teorema, as hipóteses incluem l < u, A > 0, H >= 2, M >= 0,
Clow >= 0, cF > 0, diferenciabilidade e |f'| <= M no intervalo pai,
`HasSourceSupply`, `HasUniformDangerBound`, e

```text
Clow H^(-98) <= (cF/4) * ((u-l)/3).
```

O limiar de contagem é independente de H, conforme a etapa 2. O teorema
escolhe Q acima desse limiar e de um `Qmin` arbitrário, preservando
Q <= r.den < 2Q. Para uma futura recursão, `Qmin = 2*q_previous+1`
permite impor o crescimento dos denominadores do artigo.

Os campos de `SuccessorInterval` certificam:

| Campo | Propriedade do intervalo filho |
| --- | --- |
| `nondegenerate` | Comprimento estritamente positivo |
| `nested` | Inclusão no interior do pai |
| `length` | Comprimento exato R/(#Z+2) |
| `avoids` | Nenhum ponto pertence a Z |
| `source` | 0 < |x-r| < r.den^(-A) em todo o filho |
| `cutoff_increases` | H < T_next |
| `target` | |f(x)-a/b| > b^(-100) para todo inteiro a e H <= b < T_next |
| `tail` | Condição de cauda válida no próximo terço médio |

## Verificação e pendências

São 14 novos teoremas, todos listados em `scripts/Audit.lean`, totalizando
37 teoremas explicitamente declarados. As declarações e suas ligações
com o artigo estão também listadas no README. Os testes realizados estão
registrados em `VALIDATION.md`.

Faltam a inicialização e a recursão que produzem a sequência infinita,
o tratamento analítico dos conjuntos de zeros, a prova da oferta de
racionais (Lema 2.2), a Proposição 5.1 e suas dependências. A unicidade
do ponto de interseção e uma formulação via expoente de irracionalidade
também não são afirmadas nesta atualização. Os Teoremas 1.1 e 1.2 ainda
não estão formalizados integralmente.

## Aplicação e commit

Na pasta do projeto, aplique `MahlerLean-step4.patch` com `git apply`,
após executar `git apply --check`. Execute então `bash scripts/check.sh`.
Não é preciso copiar manualmente os módulos nem executar `lake update`.

Mensagem sugerida para o commit local:

```text
Formalize one fusion step from counting hypotheses
```

Esta atualização não publica o projeto no GitHub.
