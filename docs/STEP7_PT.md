# Etapa 7 — Oferta de Farey com constante 1/4

Referência: `paper/main.tex`, enviado em 18 de setembro de 2026,
SHA-256 `4ac94b1f36e6a48103b25344e8e736657cef2cb5944c600c5afe098119f8b995`.
O manuscrito e as revisões fixadas de Lean/mathlib não foram alterados.

## Resultado

O Lema 2.2 está demonstrado, com a constante absoluta do artigo:

```text
Para todo l < u, existe Q0 > 0 tal que, para todo natural Q >= Q0,
  #(sourceFractions l u Q) >= (1/4) (u-l) Q^2.
```

Os racionais são contados uma única vez, usando o denominador reduzido
canônico no bloco `[Q,2Q)`. Os extremos l,u são reais arbitrários;
o intervalo pode conter números negativos e zero. O limiar depende do
intervalo, mas a constante 1/4 não depende dele.

Declarações finais:

- `sourceFractions_quarter_supply`: prova `HasSourceSupply l u (1/4)`.
- `exists_source_supply_threshold`: explicita a positividade de Q0.
- `exists_escape_of_uniform_counting`: aplica a oferta provada à fusão.

## Uma prova elementar do mesmo enunciado

O artigo usa as assintóticas clássicas da soma de phi e do número de
divisores. A prova Lean abaixo demonstra o mesmo enunciado por cotas
finitas mais grosseiras. Não afirmamos ter formalizado o coeficiente
assintótico 9/pi^2, e o texto do artigo não foi modificado.

### 1. Contagem por denominador e inversão de Möbius

`reducedNumerators l u q` enumera os inteiros p entre ceil(lq) e floor(uq)
com gcd(|p|,q)=1. A prova trata separadamente o fato de q ser positivo.
Para qualquer intervalo real fechado não vazio, a contagem de inteiros
difere de seu comprimento por no máximo 1. A contagem dos múltiplos de d
é a contagem de inteiros no intervalo com extremos divididos por d.

O indicador de coprimalidade é escrito como a soma de mu(d) sobre os
divisores comuns de p e q. A troca de duas somas finitas dá a fórmula
exata de Möbius. Juntamente com |mu(d)| <= 1 e a identidade da totiente,
ela fornece, com constante explícita um,

```text
|N_q([l,u]) - (u-l) phi(q)| <= #divisors(q).
```

A decomposição de `sourceFractions` em fibras do denominador prova
que sua cardinalidade é exatamente a soma de N_q no bloco. Portanto,

```text
#source >= (u-l) sum_{Q<=q<2Q} phi(q)
           - sum_{Q<=q<2Q} #divisors(q).
```

### 2. Cota inferior elementar da soma das totientes

Todo par não coprimo em `[1,N]^2` possui um divisor primo comum.
Esse divisor é pelo menos 2 e é diferente de 4. Para d fixo existem
floor(N/d)^2 pares cujas duas coordenadas são divisíveis por d.
Usamos a união dessas condições, sem supor que sejam disjuntas.

A soma dos recíprocos dos quadrados de todos os inteiros d>=2 diferentes
de 4 é limitada superiormente por

```text
1/4 + 1/9 + sum_{d>=5} 1/(d(d-1)) = 11/18.
```

No Lean, apenas a versão finita é utilizada. A cauda é telescópica e
não exige construir uma série infinita. Assim, os pares coprimos
ocupam pelo menos 7/18 do quadrado. A reflexão pela diagonal e a
contagem no triângulo por phi(q) dão

```text
sum_{q=1}^N phi(q) >= (7/36) N^2.
```

Por outro lado, phi(q)<=q fornece o limite superior N(N+1)/2.
Subtraindo as somas iniciais e tratando o extremo 2Q, obtemos

```text
sum_{Q<=q<2Q} phi(q) >= (5/18) Q^2 - (5/2) Q.
```

### 3. Erro dos divisores e conclusão

Emparelhar cada divisor d de n com n/d mostra

```text
#divisors(n) <= 2 floor(sqrt(n)).
```

Como o bloco tem Q denominadores e q<2Q, seu erro total é no máximo
`2 Q floor(sqrt(2Q))`. Para L=u-l>0, concluímos a estimativa finita

```text
#source >= L ((5/18) Q^2 - (5/2) Q) - 2 Q floor(sqrt(2Q)).
```

Basta escolher um natural N > 41472/L^2 e Q0=max(180,N).
Para Q>=Q0, temos `144 floor(sqrt(2Q)) <= L Q`.
Os dois termos de erro são, cada um, no máximo L Q^2/72.
Como 5/18 - 1/36 = 1/4, segue exatamente o Lema 2.2.
Esses limiares não foram otimizados.

## Ligação com a fusão

`UniformCountingInputs f` conserva os dados analíticos, os conjuntos
finitos proibidos e a cota uniforme para as fontes perigosas. Não tem
campo `supply` nem parâmetro livre cF. A definição `toFusionInputs`
insere cF=1/4 e o teorema de oferta demonstrado nesta etapa.

`exists_escape_of_uniform_counting` constrói o ponto de Liouville e
prova a desigualdade eventual de aproximação para sua imagem, com
expoente 100, e que essa imagem não é Liouville. A conclusão ainda é
condicional à cota de fontes perigosas e aos dados analíticos explícitos.

Não estão demonstrados nesta etapa: a Proposição 5.1, a construção
analítica dos zeros de Wronskianos, as estimativas uniformes de subníveis,
o argumento de determinantes, nem os Teoremas 1.1 e 1.2 completos.

## Verificação e envio

São quatro módulos novos, com 26 novos teoremas: o total do projeto
passa de 55 a 81 teoremas nomeados e auditados, em 17 módulos.
A verificação efetivamente executada está registrada em `VALIDATION.md`.

Aplique `MahlerLean-step7.patch` com `git apply --check` e `git apply`.
Para obter os módulos adicionais de mathlib:

```bash
lake exe cache get Mathlib.NumberTheory.ArithmeticFunction Mathlib.Data.Nat.Totient
bash scripts/check.sh
```

Mensagem do commit:

```text
Prove Farey source supply with constant one quarter and discharge fusion input
```

Depois de criar o commit, `git push` o envia para o repositório privado
`DiegoMarquesMath/MahlerLean` e inicia uma nova verificação no GitHub.
O repositório existe, mas o acesso conectado nesta sessão permanece
na conta DiegoNash; o envio deste patch depende do terminal autenticado
como DiegoMarquesMath ou da correção da conexão do GitHub nesta sessão.
