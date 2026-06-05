import json

with open("espagne_frontera_sur/geocode_cache.json", encoding="utf-8") as f:
    cache = json.load(f)

too_vague = {
    "marruecos", "argelia", "senegal", "mauritania", "mali", "niger", "chad",
    "tchad", "nigeria", "gambia", "guinea", "guinea bissau", "guinea-bissau",
    "guinea conakri", "sierra leona", "liberia", "costa de marfil", "burkina faso",
    "ghana", "togo", "benin", "camerun", "cameroun", "libia", "libye", "tunez",
    "tunisie", "egipto", "egipte", "turquia", "turquie", "grecia", "grece",
    "italia", "france", "francia", "espana", "espagne", "portugal", "marocco",
    "cabo verde", "cap vert", "canarias", "sahara", "sahara occidental",
    "sahara occid", "subsahariano", "subsahariana",
}

removed = []
for key in list(cache.keys()):
    base = key.split(" | ")[0].strip()
    if base in too_vague and cache[key] is not None:
        removed.append((key, cache[key]))
        del cache[key]

with open("espagne_frontera_sur/geocode_cache.json", "w", encoding="utf-8") as f:
    json.dump(cache, f, ensure_ascii=False, indent=2)

print(f"Entrées supprimées: {len(removed)}")
for key, val in removed:
    print(f"  {key!r}: {val}")
print("Done.")



