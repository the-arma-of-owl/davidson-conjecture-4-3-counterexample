# Üsleri 0–79 arasında sonlu bir tanık

Bu incelemede türetilen argüman, deponun Lean teoremi prop3'ü kullanır. Aşağıdaki yeni adımlar yazılı ispattır. Kod, son bölümdeki sayısal üst sınırı kesin aritmetikle hesaplar.

## Hangi graf?

B = {−10,…,10}⁸⁰ ve π(x) = ∑ᵢ xᵢ αⁱ olsun. Köşeleri π(B) alın. B içinde kalan her x, x+eᵢ çifti için görüntülerini bir kenarla birleştirin ve çakışan köşeleri tek köşe sayın. Bu, Γ'nın sonlu bir altgrafını açık bir formülle verir. Her kenarın farkı izin verilen ±αⁱ adımlarından biridir. Aşağıda üç rengin yetmediğini gösteriyoruz. Dört rengin yetmesi ana grafik için Davidson Teorem 4.1'den gelir.

## Neden üç renge boyanamaz?

1. A, xʲf'nin katsayı vektörlerini satır olarak içeren 68 × 80 tamsayı matrisi olsun. ℓⱼ satırları için π(ℓⱼ)=0. Her satırın katsayı toplamı 1, mutlak değerler toplamı 19, her sütunun mutlak değerler toplamı en çok 19'dur.
2. Üç boyamayı π ile B'ye çekelim. Birim adımda renk farkının mod 3'teki ±1 temsilcisini kullanalım. Birim karenin çevresinde farkların toplamı çifttir, üçün katıdır ve mutlak değeri en çok 4'tür. Dolayısıyla sıfırdır. Kutunun kareleri bütün kapalı yürüyüşleri geri dönüş silme ve bitişik farklı koordinat adımlarını değiştirme yoluyla üretir. Böylece kutuda, birim kenarda ±1 değişen bir tamsayı yüksekliği h vardır. B ∩ (B−ℓⱼ) boş olmayan bir tamsayı kutusudur ve bağlantılıdır. Bu kesişimde x ve x+ℓⱼ aynı renktedir. Birim kenar renk farkları da bu ötelemeyle aynıdır. Bundan h(x+ℓⱼ)−h(x) farkının kesişimde sabit olduğu çıkar. Buna tⱼ diyelim. Renk mod 3'te korunduğu, 0'dan ℓⱼ'ye 19 adımlık bir yol bulunduğu için tⱼ, 3'ün tek katıdır ve |tⱼ|≤19'dur.
3. Herhangi bir m∈ℤ⁶⁸ ve z=Aᵀm alalım. Her j için |mⱼ| tane sgn(mⱼ)ℓⱼ sıçraması, her i için |zᵢ| tane −sgn(zᵢ)eᵢ adımı kullanalım. Bütün hareketlerin vektörel toplamı sıfırdır. N kopyası olan her hareket türünü (k−½)/N zamanlarına yerleştirelim (k=1,…,N). Sıfır kopyası olan türleri atlarız. Bütün türleri zamana göre sıralayalım. Eşzamanlı olayları dilediğimiz sırayla işleyebiliriz.
4. Bir olayın zamanı u iken her türün gerçekleşen kopya sayısı uN'den en çok ½ sapar. Bu, eşzamanlı kopyaları işlemenin ortasında da geçerlidir. İdeal ağırlıklı toplam sıfır olduğundan gerçek konumun i. koordinatının mutlak değeri en çok (∑ⱼ|ℓⱼᵢ|+1)/2 ≤ 10'dur. Böylece her başlangıç ve bitiş konumu **aynı B kutusunda** kalır. Bir sıçramanın yükseklik farkı 2. adımdan ±tⱼ'dir. İstenirse sıçrama iki uç arasında kutunun içinde kalan 19 birim adımla açılabilir. Kapalı turun yükseklik farkları sıfıra toplandığından **|m·t|≤‖Aᵀm‖₁** elde edilir.
5. Payda temizleme ve süreklilik bu eşitsizliği tüm reel m'lere taşır. A[−1,1]⁸⁰ kompakt ve konvekstir. m yönündeki destek değeri tam ‖Aᵀm‖₁'dir. Ayırma teoremi t∈A[−1,1]⁸⁰ verir. Bu, depoda doğrulanan Önerme 3 ile çelişir.

## Görüntüdeki tepe sayısı

Her kutu elemanını bir tamsayı polinomu olarak yazalım. Derece 79'dan 12'ye doğru, her yüksek katsayıyı 2'ye bölüp kalanı rₖ∈{0,1} bırakan sayıda X^(k−12)f çıkaralım. Bu, α'daki değeri korur. En çok 2⁶⁸ yüksek basamak deseni vardır. Alçak basamaklar 12 tamsayı uᵢ'dir.

Rₖᵢ, Xᵏ'nin f ile ℚ[X]'te bölümünden kalanın Xⁱ katsayısı olsun. Yüksek basamak deseni sabitlenince uᵢ = ∑ₖ xₖ Rₖᵢ − ∑ₖ₌₁₂⁷⁹ rₖ Rₖᵢ'dir. Burada xₖ başlangıç köşesinin −10 ile 10 arasındaki katsayısıdır. Dolayısıyla uᵢ için olası tamsayı sayısı en fazla ⌊20∑ₖ|Rₖᵢ|⌋+1'dir. Bu 12 sayının çarpımını 2⁶⁸ ile çarpmak toplam köşe sayısını yukarıdan sınırlar. Farklı temsillerin farklı köşeler olması gerekmez. Sonuç **7,948 × 10⁵²'den küçüktür**. Tam tamsayı ve ara değerler için bound.txt dosyasına bakın.

Bu, minimum boyut tahmini değildir. Belirtilen altgrafın tamamını bellekte üretmedik. Matematiksel olarak formülle verilen bir tanık ile okunabilir boyutta, tek tek listelenmiş bir tanık ayrı hedeflerdir.

## Pratik arama için iki zorunlu koşul

- Her bağlantılı adayın en küçük üssü m ve en büyüğü M ise, bir köşeyi sıfıra öteleyip αᵐ'ye bölmek onu G_(M−m)'nin içine taşır. Üs aralığı ≤78 olan her bileşen dolayısıyla üç renge boyanabilir.
- Özellikle G₇₉ içinde M₇₈'in iki koseti vardır. Son kaydırılmış bağıntı 2α⁷⁹∈M₇₈ verir. Öte yandan α⁷⁹∈M₇₈ olsaydı α bir monik tamsayı polinomunun kökü olurdu. İki katmanın her biri üç renge boyanabilir ve yalnız ±α⁷⁹ kenarları katman değiştirir. İlk katmanın renkleri sabitken bir çapraz kenar öbür katmanın altı renk permütasyonundan ikisini yasaklar. İki kenar en çok dördünü yasaklar. Demek ki G₇₉'daki bir engel en az üç çapraz kenar gerektirir. Bu son koşul üsleri 79 ile sınırlı arama içindir.
