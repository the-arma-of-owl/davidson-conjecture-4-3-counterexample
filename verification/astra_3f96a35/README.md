# Davidson 3f96a35 denetimini yeniden çalıştırma

Hedef commit: 3f96a3543eca8117d7b18ffb1ae80778e7d77206. Lean 4.37.0-rc1, Mathlib v4.37.0-rc1. Depo bağımlılıklarının kesin sürümleri lean/lake-manifest.json içindedir. Aşağıdaki komutlar Bash, Lean/Lake (örneğin elan ile), git, Python 3.10+, curl, tar ve sha256sum kullanır. Komutlara ZIP'in açıldığı klasörde başlayın. Python'u normal modda çalıştırın; bazı denetimler assert kullanır.

## Lean ve sertifika

```bash
git clone https://github.com/the-arma-of-owl/davidson-conjecture-4-3-counterexample repo
git -C repo checkout --detach 3f96a3543eca8117d7b18ffb1ae80778e7d77206
cd repo/lean
python3 tools/convert_cert.py ../certificate/proof_fB_L68.jsonl.gz DavidsonLean/data/cert_L68.txt
sha256sum DavidsonLean/data/cert_L68.txt
lake exe cache get
lake build
lake env lean DavidsonLean/Conjecture.lean
lake env lean ../../Audit.lean
lake env lean DavidsonLean/Test_Corrupt.lean
cd ../..
```

Beklenen SHA-256: 89632a5f190cf60b3adbdeffcbb3d83bc6e7da10140d4d629aa38e6b1439054b. İki olumsuz test satırında toplam altı false beklenir. Test dosyası sonuçları yazdırır; çıktıyı ayrıca kontrol edin. Build logundaki linter ve modül sistemi uyarıları işlemi başarısız kılmadı.

## Bağımsız hesaplar ve arama pilotu

```bash
python3 -m venv .venv
source .venv/bin/activate
python -m pip install sympy 'python-sat==1.9.dev25'
python repo/verification/astra/davidson.py repo
python witness_bound.py
curl -fLsS https://arxiv.org/src/2610.09474v1 -o davidson-arxiv.tar
tar -xOf davidson-arxiv.tar anc/sextic-witness.csv > sextic-witness.csv
python pilot.py --csv sextic-witness.csv
```

CSV olmadan python pilot.py, 830 tepeli kör kalibrasyonu ve yeni adayın tamamını çalıştırır. Aday kenarları, rasyonel polinom kalanları ortak paydaya getirilerek tam tamsayı koordinatlarında oluşturulur. SAT=True sonucunda çıkarılan renkler her kenarda ayrıca denetlenir. SAT=False'un pozitif kontrolü, özgün sekstik için de yayımlanmış bir sonuçtur. Yeni polinom için bir UNSAT çıktısı elde edilmedi. --csv seçeneği yayımlanan 24 tepeli grafı ayrıca denetler; kör çekirdek çıkarımı bu dosyaya bakmaz. Buradaki pilot için ayrı LRAT ispat dosyası üretilmedi. pilot.txt süreleri tek koşuya ait duvar saatidir ve makineye göre değişir.

## Sonlu graf açıklaması

sonlu_tanik.md, grafik tanımını, sınırlı kutuda yükseklik ispatını, köşe sayısı hesabını ve iki katmanlı arama koşulunu içerir. witness_bound.py yalnızca yazılı ispatın sayısal üst sınırını yeniden hesaplar.

## 68 koşulun tek tek zorunluluğu

omission_witnesses.json, her j=0,…,67 için 80 rasyonel sayı içerir. Bu noktada kutu ve j dışındaki bütün koşullar sağlanır. j koşulu sağlanmaz. Denetim için ek paket gerekmez.

```bash
python check_omissions.py
```

Yeni çözümler aramak isterseniz aşağıdaki komutlar, K=78 kelimesinden önek/son ek adayları üretir, gerektiğinde karışık tamsayılı programlama kullanır ve sonucu tam kesirlerle denetler. LP çözümünün ilk 12 serbest koordinatı ve atlanan satıra karşılık gelen koordinat rasyonelleştirilir; diğer koordinatlar yinelemeden **kesin** üretilir. Zaman sınırı çözücünün hızına göre artırılabilir.

```bash
python -m pip install scipy numpy
python find_omissions.py repo --seconds 3 --output regenerated_omissions.json
```

Böylece 68 satırlık olanaksız sistemin içerme bakımından minimal olduğu ayrıca kanıtlanır. Bu ifade yalnızca satırların tek tek kaldırılmasını anlatır; başka bir kanıtın 68 satıra veya bir tanığın 68 köşeye ihtiyaç duyduğunu söylemez.
